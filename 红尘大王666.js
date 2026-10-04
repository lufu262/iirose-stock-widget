// ==UserScript==
// @name         iirose 股票走势图（网站/桌面/APK 通用插件）
// @namespace    hcdw666.iirose.stock
// @version      1.0.0
// @description  在 iirose 页面（网页版 / Electron 桌面壳 / 任意 WebView）注入股票走势图：实时捕获行情帧，绘制 股价/总股/总金 三线走势图 + 均线 + 崩盘重置点，提示距下次股价变动，完整轮数据自动保存。
// @match        https://iirose.com/*
// @match        https://www.iirose.com/*
// @match        https://lab.iirose.com/*
// @match        https://*.iirose.com/*
// @run-at       document-start
// @grant        none
// ==/UserScript==

/* ============================================================
 * iirose 股票走势图插件（单文件、零依赖、三端通用）
 * - 网页版：Tampermonkey 安装（上方元数据，已含 iframe 注入），自动捕获页面行情
 * - 桌面版：iirose Electron 壳（加载同一 https://iirose.com），
 *   打开 DevTools（F12）→ Console → 粘贴本文件全部代码回车即可
 * - APK/WebView：把本文件放入工程 www/ 目录后 <script src> 引入，
 *   宿主可通过 window.iiStockSource = fn(text) 推送行情帧
 *
 * 数据源（网页版实测）：iirose 网页版股票数据走 XHR 轮询接口，且房间内容
 *   在 iframe 内，部分实时通道走 WebSocket——插件同时补丁 XHR / fetch /
 *   WebSocket 三条通道（含 iframe，捕获后 postMessage 转发顶层），
 *   自动识别任意通道返回的行情帧，无需配置。
 *
 * 协议（iirose 股票行情帧，与红尘大王666 2.0 一致）：
 *   '>'"总股>总金>[新股价]>个人股>个人金'   —— 按引号 split：5 段=股价变动帧
 *   4 段=平盘帧（沿用上次股价）；'>#'=查询；'>$n'=买入；'>@n'=卖出
 *   本轮起点：股价=1、总股=1000、总金=1000；崩盘重置判定：
 *   unitPrice===1 && totalStock===1000
 * ============================================================ */
function widgetMain(global) {
  'use strict';

  /* ---------------- 配置与常量 ---------------- */
  var CFG = {
    key: 'hcdw6_stock_widget',
    roundsKey: 'hcdw6_stock_rounds_v2',
    maxPoints: 50,          // 走势图仅保留最近 50 个股价变化点
    maxSavedRounds: 20,     // localStorage 最多缓存完整轮数
    intervalW: 0.7,         // 距下次变动：中位数权重
    intervalLast: 0.3       // 距下次变动：最近一次权重
  };
  var RANGE_LABEL = { round: '当前轮', 5: '近5跳', 10: '近10跳' };

  /* ---------------- 工具函数 ---------------- */
  function $(id) { return document.getElementById(id); }
  function el(tag, cls, html) { var e = document.createElement(tag); if (cls) e.className = cls; if (html !== undefined) e.innerHTML = html; return e; }
  function ns(tag) { return document.createElementNS('http://www.w3.org/2000/svg', tag); }
  function fmtP(v) { v = Number(v); if (isNaN(v)) return '—'; return v < 0.1 ? v.toFixed(4) : (v < 1 ? v.toFixed(3) : v.toFixed(2)); }
  function fmtN(v) { v = Number(v); if (isNaN(v)) return '—'; return v >= 10000 ? (v / 10000).toFixed(2) + '万' : (v >= 1000 ? (v / 1000).toFixed(1) + 'k' : String(Math.round(v))); }
  function fmtMoney(v) { v = Number(v); if (isNaN(v)) return '—'; return v >= 10000 ? (v / 10000).toFixed(2) + '万' : v.toLocaleString('zh-CN'); }
  function pct(a, b) { a = Number(a); b = Number(b); if (isNaN(a) || isNaN(b) || !b) return '—'; var d = (a - b) / Math.abs(b) * 100; return (d >= 0 ? '+' : '') + d.toFixed(2) + '%'; }
  function esc(s) { return String(s == null ? '' : s).replace(/[&<>"']/g, function (c) { return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]; }); }
  function now() { return Date.now(); }
  function median(arr) { if (!arr.length) return null; var a = arr.slice().sort(function (x, y) { return x - y; }); var m = a.length >> 1; return a.length % 2 ? a[m] : (a[m - 1] + a[m]) / 2; }

  /* ---------------- 状态 ---------------- */
  var S = {
    started: false,
    running: false,
    lastStock: null,        // {unitPrice,totalStock,totalMoney,personalStock,personalMoney,hasPrice}
    lastChangeTs: 0,        // 最近一次「股价变化」时间戳
    cycleStep: 0,           // 本轮周期步数（仅股价变化计数）
    roundNo: 1,             // 当前轮号
    ticks: [],              // 全量变化记录 {ts,price,stock,money,event,cycle}
    round: [],              // 当前轮记录
    savedRounds: [],        // 已封存的完整轮 [{start,end,ticks}]
    intervals: [],          // 股价变化间隔序列（ms）
    range: 'round',         // 走势范围
    lastEvt: '—',
    lastTsText: '—',
    connText: '等待数据…'
  };

  /* ---------------- 帧解析 ---------------- */
  // 输入：服务器文本帧。返回行情对象或 null
  function parseFrame(text) {
    if (typeof text !== 'string') return null;
    var t = text;
    // 行情帧形如：>"总股>总金>[新股价]>个人股>个人金（5 段=变动；4 段=平盘沿用上次价）
    if (t.charAt(0) === '>') {
      var qi = t.indexOf('"');
      if (qi >= 0) {
        var payload = t.slice(qi + 1);
        var segs = payload.split('>');
        if (segs.length >= 4) {
          var nums = segs.map(function (x) { return parseFloat(x); });
          var hasPrice = nums.length >= 5 && !isNaN(nums[2]);
          return {
            totalStock: Math.round(nums[0]),
            totalMoney: nums[1],
            unitPrice: hasPrice ? nums[2] : (S.lastStock ? S.lastStock.unitPrice : null),
            personalStock: hasPrice ? Math.round(nums[3]) : Math.round(nums[2]),
            personalMoney: hasPrice ? nums[4] : nums[3],
            hasPrice: hasPrice
          };
        }
      }
      return null; // 非行情控制帧（如 ># 查询指令回声）
    }
    return null;
  }

  /* ---------------- 数据引擎 ---------------- */
  function onFrame(st) {
    if (!st || st.totalStock == null || st.totalMoney == null) return;
    var lastT = S.ticks[S.ticks.length - 1];
    // 网页版轮询会重复推送相同帧：内容完全一致时忽略（不算变动、不记录）
    if (lastT && lastT.price === st.unitPrice && lastT.stock === st.totalStock && lastT.money === st.totalMoney) {
      S.lastStock = st; return;
    }
    var prev = S.lastStock;
    var atStart = st.unitPrice === 1 && st.totalStock === 1000;
    var isReset = atStart && !!prev && (prev.unitPrice !== 1 || prev.totalStock !== 1000); // 从别的状态回到起点=崩盘重置
    var firstStart = atStart && !prev; // 首帧即起点：第 1 轮开始，不封轮、不加轮号
    if (isReset) {
      sealRound(now());
      S.roundNo++;
      S.cycleStep = 0;
      S.round = [];
      S.lastEvt = 'R';
    } else {
      S.lastEvt = firstStart ? 'R' : (st.hasPrice ? 'U' : 'F');
    }
    var priceChanged = (isReset || firstStart) ? false : (prev ? (st.hasPrice && Number(st.unitPrice) !== Number(prev.unitPrice)) : true);
    if (priceChanged) {
      if (prev && prev.hasPrice && prev.unitPrice != null && st.unitPrice != null) {
        S.intervals.push(Math.max(1, now() - S.lastChangeTs));
        if (S.intervals.length > 60) S.intervals.shift();
      }
      S.lastChangeTs = now();
      S.cycleStep++;
    } else if (firstStart) {
      S.lastChangeTs = now();
    }
    S.lastStock = st;
    var tick = {
      ts: now(), price: st.unitPrice, stock: st.totalStock, money: st.totalMoney,
      event: (isReset || firstStart) ? 'R' : 'U', cycle: S.cycleStep
    };
    S.ticks.push(tick);
    if (S.ticks.length > 20000) S.ticks.shift();
    S.round.push(tick);
    S.lastTsText = new Date(tick.ts).toLocaleTimeString('zh-CN', { hour12: false });
    S.running = true;
    scheduleRender();
  }

  function sealRound(endTs) {
    if (!S.round.length) return;
    S.savedRounds.push({ start: S.round[0].ts, end: endTs, n: S.round.length, ticks: S.round.slice() });
    if (S.savedRounds.length > CFG.maxSavedRounds) S.savedRounds.shift();
    try { localStorage.setItem(CFG.roundsKey, JSON.stringify(S.savedRounds)); } catch (e) {}
  }

  /* ---------------- 距下次股价变动（仅股价变化间隔统计） ---------------- */
  function nextChange() {
    var iv = S.intervals.slice();
    if (iv.length < 2) return null;
    var md = median(iv);
    var last = iv[iv.length - 1];
    return Math.round(md * CFG.intervalW + last * CFG.intervalLast);
  }

  /* ---------------- 走势数据 ---------------- */
  function buildSeries() {
    var base = S.ticks;
    if (S.range === 'round') {
      var rIdx = -1;
      for (var i = base.length - 1; i >= 0; i--) { if (base[i].event === 'R') { rIdx = i; break; } }
      if (rIdx >= 0) base = base.slice(rIdx);
      else base = base.slice(-CFG.maxPoints);
    } else if (typeof S.range === 'number' && S.range > 0) {
      // 近 N 跳 = 最近 N 次股价变化：先压成 priceSeq 再截尾
      var ps = priceSeq(base);
      base = base.slice(Math.max(0, base.length - S.range * 3)); // 取足够原始段，下方再严格截
      var ps2 = priceSeq(base);
      var lastN = ps2.slice(-S.range);
      if (lastN.length) {
        var cutTs = lastN[0].ts;
        var idx = 0;
        for (; idx < base.length; idx++) if (base[idx].ts >= cutTs) break;
        base = base.slice(idx);
      }
    }
    // 每次股价变化 = 一个数据点；同一价格内多次变化只留最新
    var ps = priceSeq(base);
    if (ps.length > CFG.maxPoints) ps = ps.slice(-CFG.maxPoints);
    var labels = [], prices = [], stocks = [], moneys = [], resets = [];
    for (var k = 0; k < ps.length; k++) {
      var t = ps[k];
      labels.push(new Date(t.ts).toLocaleTimeString('zh-CN', { hour12: false }));
      prices.push(t.price);
      stocks.push(t.stock);
      moneys.push(t.money);
      if (t.event === 'R') resets.push(k);
    }
    // 均线
    function ma(w) {
      var out = [];
      for (var i2 = 0; i2 < prices.length; i2++) {
        if (i2 < w - 1) { out.push(null); continue; }
        var s2 = 0, n2 = 0;
        for (var j2 = 0; j2 < w; j2++) { var v = prices[i2 - j2]; if (v == null) break; s2 += v; n2++; }
        out.push(n2 === w ? s2 / w : null);
      }
      return out;
    }
    return { labels: labels, prices: prices, stocks: stocks, moneys: moneys, resets: resets, ma5: ma(5), ma10: ma(10), ma20: ma(20) };
  }

  // 按「股价变化」压平：连续相同价格的 tick（仅股数/总金变化）不产生新点
  function priceSeq(arr) {
    var out = [];
    for (var i = 0; i < arr.length; i++) {
      var t = arr[i];
      if (!out.length || out[out.length - 1].price !== t.price) out.push({ ts: t.ts, price: t.price, stock: t.stock, money: t.money, event: t.event });
      else out[out.length - 1] = { ts: t.ts, price: t.price, stock: t.stock, money: t.money, event: t.event };
    }
    return out;
  }

  /* ---------------- SVG 走势图渲染 ---------------- */
  function renderChart(host, d) {
    host.innerHTML = '';
    if (!d.prices.length) {
      host.appendChild(el('div', 'iw-ph', '等待行情数据…（登录进入房间后自动绘制）'));
      return;
    }
    var W = 340, H = 200, padL = 40, padR = 46, padT = 10, padB = 18;
    var iw = W - padL - padR, ih = H - padT - padB;
    var svg = ns('svg');
    svg.setAttribute('viewBox', '0 0 ' + W + ' ' + H);
    svg.setAttribute('width', '100%');
    svg.setAttribute('height', '100%');
    var defs = ns('defs');
    svg.appendChild(defs);
    // 网格 + 股价刻度（左轴）
    function yOfPrice(v) { var mn = Math.min.apply(null, d.prices), mx = Math.max.apply(null, d.prices); if (mx === mn) { mx = mn + 1; } return padT + (1 - (v - mn) / (mx - mn)) * ih; }
    function yOf(v, arr) { var mn = Math.min.apply(null, arr), mx = Math.max.apply(null, arr); if (mx === mn) { mx = mn + 1; } return padT + (1 - (v - mn) / (mx - mn)) * ih; }
    for (var g = 0; g <= 4; g++) {
      var gy = padT + ih * g / 4;
      var gl = ns('line');
      gl.setAttribute('x1', padL); gl.setAttribute('x2', W - padR);
      gl.setAttribute('y1', gy); gl.setAttribute('y2', gy);
      gl.setAttribute('stroke', '#1e293b'); gl.setAttribute('stroke-width', 0.5);
      svg.appendChild(gl);
      var gv = Math.min.apply(null, d.prices) + (Math.max.apply(null, d.prices) - Math.min.apply(null, d.prices)) * (1 - g / 4);
      var tx = ns('text');
      tx.setAttribute('x', padL - 4); tx.setAttribute('y', gy + 3);
      tx.setAttribute('text-anchor', 'end'); tx.setAttribute('font-size', 8); tx.setAttribute('fill', '#94a3b8');
      tx.textContent = fmtP(gv);
      svg.appendChild(tx);
    }
    // X 轴标签（首尾）
    var firstL = ns('text'), lastL = ns('text');
    firstL.setAttribute('x', padL); firstL.setAttribute('y', H - 4); firstL.setAttribute('font-size', 7.5); firstL.setAttribute('fill', '#64748b');
    firstL.textContent = d.labels[0];
    lastL.setAttribute('x', W - padR); lastL.setAttribute('y', H - 4); lastL.setAttribute('text-anchor', 'end'); lastL.setAttribute('font-size', 7.5); lastL.setAttribute('fill', '#64748b');
    lastL.textContent = d.labels[d.labels.length - 1];
    svg.appendChild(firstL); svg.appendChild(lastL);
    // 折线生成
    function polyline(arr, key, color, wdt) {
      var pts = [];
      for (var i = 0; i < arr.length; i++) {
        if (arr[i] == null || isNaN(Number(arr[i]))) continue;
        var x = padL + (i / Math.max(1, arr.length - 1)) * iw;
        var y = key === 'p' ? yOfPrice(Number(arr[i])) : yOf(Number(arr[i]), arr);
        pts.push(x.toFixed(1) + ',' + y.toFixed(1));
      }
      if (pts.length < 2) return null;
      var pl = ns('polyline');
      pl.setAttribute('points', pts.join(' '));
      pl.setAttribute('fill', 'none'); pl.setAttribute('stroke', color); pl.setAttribute('stroke-width', wdt);
      pl.setAttribute('stroke-linejoin', 'round'); pl.setAttribute('stroke-linecap', 'round');
      return pl;
    }
    // 均线（股价归一）
    [['ma5', '#f59e0b', 1], ['ma10', '#38bdf8', 1], ['ma20', '#a78bfa', 1]].forEach(function (mv) {
      var pts = [];
      var arr = d[mv[0]];
      for (var i = 0; i < arr.length; i++) {
        if (arr[i] == null || isNaN(Number(arr[i]))) continue;
        var x = padL + (i / Math.max(1, arr.length - 1)) * iw;
        pts.push(x.toFixed(1) + ',' + yOfPrice(Number(arr[i])).toFixed(1));
      }
      if (pts.length >= 2) {
        var pl = ns('polyline');
        pl.setAttribute('points', pts.join(' '));
        pl.setAttribute('fill', 'none'); pl.setAttribute('stroke', mv[1]); pl.setAttribute('stroke-width', mv[2]);
        pl.setAttribute('opacity', 0.85);
        svg.appendChild(pl);
      }
    });
    var lp = polyline(d.prices, 'p', '#f43f5e', 1.8);
    var ls = polyline(d.stocks, 's', '#f59e0b', 1.2);
    var lm = polyline(d.moneys, 'm', '#34d399', 1.2);
    if (lp) svg.appendChild(lp);
    if (ls) svg.appendChild(ls);
    if (lm) svg.appendChild(lm);
    // 最新点高亮
    function dot(x, y, color, r) {
      var c = ns('circle');
      c.setAttribute('cx', x); c.setAttribute('cy', y); c.setAttribute('r', r);
      c.setAttribute('fill', color);
      return c;
    }
    var n = d.prices.length;
    var lx = padL + (n - 1) / Math.max(1, n - 1) * iw;
    svg.appendChild(dot(lx, yOfPrice(d.prices[n - 1]), '#f59e0b', 3));
    if (d.stocks[n - 1] != null) svg.appendChild(dot(lx, yOf(d.stocks[n - 1], d.stocks), '#f59e0b', 2.4));
    if (d.moneys[n - 1] != null) svg.appendChild(dot(lx, yOf(d.moneys[n - 1], d.moneys), '#f59e0b', 2.4));
    // 崩盘重置点（金钻）
    for (var r = 0; r < d.resets.length; r++) {
      var ri = d.resets[r];
      var rx = padL + (ri / Math.max(1, n - 1)) * iw;
      var rd = ns('rect');
      rd.setAttribute('x', rx - 3); rd.setAttribute('y', padT - 6); rd.setAttribute('width', 6); rd.setAttribute('height', 6);
      rd.setAttribute('fill', '#f59e0b'); rd.setAttribute('transform', 'rotate(45 ' + rx + ' ' + (padT - 3) + ')');
      svg.appendChild(rd);
    }
    // 右轴刻度（总股/总金 各自最新值）
    var stL = ns('text'), moL = ns('text');
    stL.setAttribute('x', W - padR + 4); stL.setAttribute('y', padT + 8); stL.setAttribute('font-size', 7.5); stL.setAttribute('fill', '#f59e0b');
    stL.textContent = '股 ' + fmtN(d.stocks[n - 1]);
    moL.setAttribute('x', W - padR + 4); moL.setAttribute('y', padT + 18); moL.setAttribute('font-size', 7.5); moL.setAttribute('fill', '#34d399');
    moL.textContent = '金 ' + fmtMoney(d.moneys[n - 1]);
    svg.appendChild(stL); svg.appendChild(moL);
    host.appendChild(svg);
  }

  /* ---------------- UI ---------------- */
  var WIDGET = null, dragState = null, renderTimer = null;

  function buildUI() {
    if (document.querySelector && document.querySelector('.iw-wrap')) return;
    var wrap = el('div', 'iw-wrap');
    wrap.innerHTML =
      '<img class="iw-mini" src="data:image/png;base64,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" title="iirose 股票走势图 · 点击展开" alt="iirose">' +
      '<div class="iw-hd"><span class="iw-t">iirose 股票走势图 <span class="iw-ico" title="行情帧自动捕获（页面 XHR/WebSocket/iframe 全通道）；一轮起点=股价1/总股1000/总金1000；仅股价变化计步与推进走势；崩盘重置=股价1且总股1000">ⓘ</span></span>' +
      '<span class="iw-fold" title="收起/展开">—</span></div>' +
      '<div class="iw-body">' +
      '<div class="iw-stats">' +
      '<div class="iw-stat"><span>连接</span><b id="iwConn">等待数据…</b></div>' +
      '<div class="iw-stat"><span>最新变化</span><b id="iwTs">—</b></div>' +
      '<div class="iw-stat"><span>本轮步数</span><b id="iwCycle">0</b></div>' +
      '<div class="iw-stat"><span>距下次变动</span><b id="iwNext">—</b></div>' +
      '</div>' +
      '<div class="iw-chart" id="iwChart"><div class="iw-ph">等待行情数据…</div></div>' +
      '<div class="iw-cards">' +
      '<div class="iw-card"><div class="k">最新股价</div><div class="v gold" id="iwPrice">—</div><div class="d" id="iwPriceD">—</div></div>' +
      '<div class="iw-card"><div class="k">最新总股</div><div class="v" id="iwStock">—</div><div class="d" id="iwStockD">—</div></div>' +
      '<div class="iw-card"><div class="k">最新总金</div><div class="v" id="iwMoney">—</div><div class="d" id="iwMoneyD">—</div></div>' +
      '</div>' +
      '<div class="iw-author">作者 <span>[*红尘一世*]</span>　ps:给我打钱</div>' +
      '</div>';
    document.body.appendChild(wrap);
    // 样式
    var css = ns('style');
    css.textContent =
      '.iw-wrap{position:fixed;right:14px;bottom:14px;z-index:999999;width:352px;max-width:94vw;background:rgba(13,17,28,.96);border:1px solid rgba(212,175,55,.4);border-radius:12px;color:#e5e7eb;font-family:system-ui,"Microsoft YaHei",sans-serif;font-size:12px;box-shadow:0 12px 40px rgba(0,0,0,.6);overflow:hidden;-webkit-user-select:none;user-select:none}' +
      '.iw-wrap *{box-sizing:border-box}' +
      '.iw-hd{display:flex;align-items:center;justify-content:space-between;padding:8px 12px;background:linear-gradient(180deg,#1a1f33,#131828);cursor:move;border-bottom:1px solid rgba(212,175,55,.25)}' +
      '.iw-t{font-weight:700;color:#f0c75e;font-size:12.5px}' +
      '.iw-ico{display:inline-block;width:14px;height:14px;line-height:14px;text-align:center;border-radius:50%;background:#2a2f45;color:#94a3b8;font-size:10px;cursor:help}' +
      '.iw-fold{color:#94a3b8;cursor:pointer;padding:0 4px;font-size:14px}' +
      '.iw-body{padding:8px 10px 10px}' +
      '.iw-stats{display:grid;grid-template-columns:1fr 1fr;gap:3px 10px;margin-bottom:6px}' +
      '.iw-stat{display:flex;justify-content:space-between;gap:6px;font-size:11px;color:#94a3b8}.iw-stat b{color:#e5e7eb;font-weight:600}' +
      '.iw-chart{background:#0b1526;border:1px solid #1e293b;border-radius:8px;padding:4px;min-height:150px;margin-bottom:6px}' +
      '.iw-ph{height:150px;display:flex;align-items:center;justify-content:center;color:#475569;font-size:11.5px}' +
      '.iw-cards{display:flex;gap:6px;margin-bottom:6px}' +
      '.iw-card{flex:1;background:#151a2b;border:1px solid #232a45;border-radius:8px;padding:6px;text-align:center}' +
      '.iw-card .k{font-size:10px;color:#8b93a7}.iw-card .v{font-size:14px;font-weight:700;margin-top:1px}.iw-card .v.gold{color:#f0c75e}.iw-card .d{font-size:9.5px;color:#64748b}' +
      '.iw-tools{display:flex;align-items:center;gap:5px}' +
      '.iw-chip{padding:3px 10px;font-size:11px;border:1px solid #2a2f45;background:#1a1f33;color:#cbd5e1;border-radius:6px;cursor:pointer}' +
      '.iw-chip.iw-on{background:#f0c75e;color:#111827;border-color:#f0c75e;font-weight:600}' +
      '.iw-author{padding:4px 8px;font-size:11px;color:#8b93a7;text-align:center;border-top:1px solid rgba(212,175,55,.22);margin-top:4px;letter-spacing:.5px}' +
      '.iw-author span{color:#f0c75e;font-weight:700}' +
      '.iw-mini{display:none;width:100%;height:100%;border-radius:14px;object-fit:cover;cursor:pointer}' +
      '.iw-min{width:54px!important;height:54px!important;padding:0!important;border-radius:14px;overflow:hidden;border-color:rgba(212,175,55,.65)!important}' +
      '.iw-min .iw-hd,.iw-min .iw-body{display:none}' +
      '.iw-min .iw-mini{display:block}' +
      '@media (max-width:480px){.iw-wrap{right:6px;bottom:6px;width:96vw}}';
    document.head.appendChild(css);
    // 事件
    wrap.querySelector('.iw-fold').addEventListener('click', function () { wrap.classList.toggle('iw-min'); });
    var mini = wrap.querySelector('.iw-mini');
    if (mini) mini.addEventListener('click', function () { wrap.classList.remove('iw-min'); });
    wrap.addEventListener('pointerdown', function (e) {
      if ((e.target.closest && e.target.closest('.iw-hd')) || (e.target.classList && e.target.classList.contains('iw-mini'))) {
        dragState = { sx: e.clientX, sy: e.clientY, ox: wrap.offsetLeft, oy: wrap.offsetTop };
        wrap.setPointerCapture && wrap.setPointerCapture(e.pointerId);
      }
    });
    wrap.addEventListener('pointermove', function (e) {
      if (!dragState) return;
      var nx = dragState.ox + (e.clientX - dragState.sx), ny = dragState.oy + (e.clientY - dragState.sy);
      nx = Math.max(0, Math.min(window.innerWidth - wrap.offsetWidth, nx));
      ny = Math.max(0, Math.min(window.innerHeight - 30, ny));
      wrap.style.left = nx + 'px'; wrap.style.right = 'auto';
      wrap.style.top = ny + 'px'; wrap.style.bottom = 'auto';
    });
    wrap.addEventListener('pointerup', function () { dragState = null; });
    WIDGET = wrap;
    refresh();
  }

  function refresh() {
    if (!WIDGET) return;
    var nx = nextChange();
    var d = buildSeries();
    var st = S.lastStock;
    var prevT = S.ticks.length >= 2 ? S.ticks[S.ticks.length - 2] : null;
    var nextEl = $('iwNext'), connEl = $('iwConn');
    if (nextEl) nextEl.textContent = nx == null ? '—' : nx + 's';
    if (connEl) connEl.textContent = S.running ? (S.lastEvt === 'R' ? '已同步·崩盘重置' : '已同步') : '等待数据…';
    if ($('iwTs')) $('iwTs').textContent = S.lastTsText;
    if ($('iwCycle')) $('iwCycle').textContent = String(S.cycleStep);
    if ($('iwPrice')) {
      $('iwPrice').textContent = st ? fmtP(st.unitPrice) : '—';
      $('iwPriceD').textContent = prevT ? pct(st.unitPrice, prevT.price) : '—';
      $('iwStock').textContent = st ? fmtN(st.totalStock) : '—';
      $('iwStockD').textContent = prevT ? pct(st.totalStock, prevT.stock) : '—';
      $('iwMoney').textContent = st ? fmtMoney(st.totalMoney) : '—';
      $('iwMoneyD').textContent = prevT ? pct(st.totalMoney, prevT.money) : '—';
    }
    renderChart($('iwChart'), d);
  }

  function scheduleRender() {
    if (renderTimer) return;
    renderTimer = setTimeout(function () { renderTimer = null; refresh(); }, 250);
  }

  /* ---------------- 数据保存与导出 ---------------- */
  function exportAll() {
    var nowTs = now();
    var lines = [];
    lines.push('=== iirose 完整轮数据 ===');
    lines.push('导出时间戳: ' + nowTs);
    lines.push('当前轮号: ' + S.roundNo + '  当前轮点: ' + S.round.length);
    lines.push('（每轮起点=股价1/总股1000/总金1000；R=崩盘重置）');
    lines.push('');
    var groups = S.savedRounds.concat([{ start: S.round.length ? S.round[0].ts : null, end: nowTs, n: S.round.length, ticks: S.round.slice(), cur: true }]);
    var gn = 0;
    for (var gi = 0; gi < groups.length; gi++) {
      var g = groups[gi];
      if (!g.ticks.length) continue;
      gn++;
      lines.push('===== 轮 ' + gn + (g.cur ? '（当前轮）' : '') + ' =====');
      lines.push('开始时间戳: ' + g.start + '   结束时间戳: ' + g.end + '   点数: ' + g.ticks.length);
      lines.push('idx\t股价\t总股\t总金\t时间戳');
      for (var ti = 0; ti < g.ticks.length; ti++) {
        var t = g.ticks[ti];
        lines.push(ti + '\t' + t.price + '\t' + t.stock + '\t' + t.money + '\t' + t.ts);
      }
      lines.push('');
    }
    var blob = new Blob([lines.join('\n')], { type: 'text/plain;charset=utf-8' });
    var a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = 'iirose完整轮数据_' + nowTs + '.txt';
    document.body.appendChild(a);
    a.click();
    setTimeout(function () { URL.revokeObjectURL(a.href); a.remove(); }, 800);
  }

  /* ---------------- 数据源适配（网页版实测：股票数据走 XHR 轮询 + 可能 iframe 内 WebSocket，需多通道全捕获） ---------------- */
  var isTop = true;
  try { isTop = global.self === global.top || global.top === global.self; } catch (e) { isTop = true; }

  // 统一入口：识别行情文本 → 本地入库渲染（iframe 内同样挂面板）；非顶层同时转发顶层备用
  function handleText(t) {
    if (typeof t !== 'string') return;
    var seg = null;
    if (t.charAt(0) === '>') seg = t;
    else { var i = t.indexOf('>"'); if (i >= 0) seg = t.slice(i); }
    if (!seg) return;
    var st = parseFrame(seg);
    if (!st) return;
    onFrame(st);
    if (!isTop) {
      try { (global.top || global.parent || global).postMessage({ __iiStockWidget: true, frame: seg }, '*'); } catch (e) {}
    }
  }

  // 通道1：补丁 WebSocket（覆盖 iframe 内实例；消息为 string 时识别）
  function patchWS() {
    var proto = global.WebSocket;
    if (!proto || proto._iirosePatched) return;
    function PWS(url, protocols) {
      var self = this;
      var real = new proto(url, protocols);
      self._real = real;
      ['bufferedAmount', 'extensions', 'protocol', 'readyState', 'url'].forEach(function (k) {
        Object.defineProperty(self, k, { get: function () { return real[k]; } });
      });
      self.send = function (d) { real.send(d); };
      self.close = function (c, r) { real.close(c, r); };
      real.addEventListener('message', function (ev) {
        var d = ev && ev.data;
        if (typeof d === 'string') handleText(d);
        if (self.onmessage) { try { self.onmessage({ data: ev.data }); } catch (e) {} }
      });
      ['open', 'close', 'error'].forEach(function (evt) {
        real.addEventListener(evt, function (ev) {
          if (self['on' + evt]) { try { self['on' + evt](ev); } catch (e) {} }
        });
      });
      return self;
    }
    PWS.prototype = proto.prototype;
    PWS.CONNECTING = 0; PWS.OPEN = 1; PWS.CLOSING = 2; PWS.CLOSED = 3;
    PWS._iirosePatched = true;
    global.WebSocket = PWS;
  }

  // 通道2：补丁 XMLHttpRequest 原型（拦截 load 后检查响应文本，不影响页面原逻辑）
  function patchXHR() {
    var X = global.XMLHttpRequest;
    if (!X || !X.prototype || X.prototype._iirosePatched) return;
    var _open = X.prototype.open, _send = X.prototype.send;
    X.prototype.open = function (m, u) { this._iwUrl = u; return _open.apply(this, arguments); };
    X.prototype.send = function (d) {
      try {
        var x = this;
        if (!x._iwHooked) {
          x._iwHooked = true;
          x.addEventListener('load', function () {
            try { handleText(x.responseText); } catch (e) {}
          });
        }
      } catch (e) {}
      return _send.apply(this, arguments);
    };
    X.prototype._iirosePatched = true;
  }

  // 通道3：补丁 fetch（响应克隆后检查文本）
  function patchFetch() {
    var F = global.fetch;
    if (!F || F._iirosePatched) return;
    global.fetch = function () {
      var args = arguments;
      return F.apply(this, args).then(function (res) {
        try {
          if (res && res.clone) {
            res.clone().text().then(function (t) { handleText(t); }).catch(function () {});
          }
        } catch (e) {}
        return res;
      });
    };
    global.fetch._iirosePatched = true;
  }

  // 通道4：iframe 转发接收（顶层监听）
  function listenBridge() {
    if (!isTop) return;
    global.addEventListener('message', function (e) {
      try {
        var d = e.data;
        if (d && d.__iiStockWidget && typeof d.frame === 'string') {
          var st = parseFrame(d.frame);
          if (st) onFrame(st);
        }
      } catch (e2) {}
    });
  }

  function setupSource() {
    if (global.iiStockSource && typeof global.iiStockSource.onFrame === 'function') {
      global.iiStockSource.onFrame = function (text) {
        var st = parseFrame(text);
        if (st) onFrame(st);
      };
      return 'bridge';
    }
    patchWS(); patchXHR(); patchFetch(); listenBridge();
    return 'ws+xhr';
  }

  /* ---------------- 启动 ---------------- */
  function autoStart() {
    if (S.started) return;
    S.started = true;
    try {
      var saved = JSON.parse(localStorage.getItem(CFG.roundsKey) || '[]');
      if (Array.isArray(saved)) S.savedRounds = saved;
    } catch (e) {}
    setupSource();
    if (!isTop) { buildUI(); return; }
    var hasFrame = false;
    try { hasFrame = !!(document.getElementById('mainFrame') || (document.querySelector ? document.querySelector('iframe#mainFrame') : null)); } catch (e) {}
    if (!hasFrame) buildUI();
  }

  return {
    autoStart: autoStart,
    mount: function (container, opts) { autoStart(); if (container) { container.appendChild(WIDGET || document.querySelector('.iw-wrap')); } },
    pushFrame: function (text) { var st = parseFrame(text); if (st) onFrame(st); return !!st; },
    getState: function () { return S; },
    exportAll: exportAll,
    parseFrame: parseFrame,
    ensureUI: function () { buildUI(); }
  };
}

/* ---------------- 启动与 iframe 自注入 ----------------
 * 网页版/桌面壳/官方APK 的聊天界面都在 <iframe id="mainFrame"> 内：
 * 插件若在顶层被加载（例如 iirose 插件/SCDN 系统），面板会被全屏 iframe 盖住，
 * 且顶层捕获不到 iframe 内的行情通道。此处把插件本体（widgetMain 源码）注入
 * iframe 同源文档运行：iframe 内自动挂面板 + 本地捕获数据。若注入失败则顶层兜底挂面板。
 * Tampermonkey 直接注入 iframe 的场景不受影响（iframe 副本自己挂面板）。
 * -------------------------------------------------------- */
if (typeof module === 'object' && module.exports) {
  if (typeof module.exports === 'undefined') module.exports = widgetMain(globalThis || {});
}
(function (root) {
  try {
    var w = widgetMain(root);
    root.IiStockWidget = w;
    var booted = false;
    function boot() {
      if (booted) return; booted = true;
      try { w.autoStart(); } catch (e) {}
    }
    if (typeof root.document !== 'undefined' && root.document.readyState !== 'loading') { boot(); }
    else if (typeof root.addEventListener === 'function') { root.addEventListener('DOMContentLoaded', function () { boot(); }); }
    else { try { boot(); } catch (e) {} }
    var isTop = true;
    try { isTop = root.self === root.top || root.top === root.self; } catch (e) {}
    if (isTop && typeof root.document !== 'undefined') {
      var tries = 0, timer = null, injected = false;
      function injectOnce() {
        try {
          var f = root.document.getElementById('mainFrame') || (root.document.querySelector ? root.document.querySelector('iframe#mainFrame') : null);
          if (!f) return false;
          var fw = f.contentWindow;
          if (!fw || !fw.document || !fw.document.createElement) return false;
          if (fw.__iiWidgetInjected) return true;
          if (fw.document.querySelector && fw.document.querySelector('.iw-wrap')) { fw.__iiWidgetInjected = true; return true; }
          var payload = 'var widgetMain=' + widgetMain.toString() + ';(function(root){var w=widgetMain(root);root.IiStockWidget=w;if(root.document&&root.document.readyState!=="loading"){try{w.autoStart();}catch(e){}}else if(root.addEventListener){root.addEventListener("DOMContentLoaded",function(){try{w.autoStart();}catch(e){}});}})(self);';
          var s = fw.document.createElement('script');
          s.textContent = payload;
          (fw.document.head || fw.document.documentElement).appendChild(s);
          fw.__iiWidgetInjected = true;
          return true;
        } catch (e) { return false; }
      }
      function loop() {
        if (injectOnce()) { if (timer) { try { root.clearTimeout(timer); } catch (e) {} } return; }
        tries++;
        if (tries >= 40) { try { w.ensureUI(); } catch (e) {} return; }  // 约20s后兜底
        if (root.setTimeout) { timer = root.setTimeout(loop, 500); }
      }
      if (root.setTimeout) { timer = root.setTimeout(loop, 600); }
    }
  } catch (e) {}
})(typeof self !== 'undefined' ? self : this);
