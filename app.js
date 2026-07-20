// pdfjsLib comes from the UMD build loaded in index.html (global)
pdfjsLib.GlobalWorkerOptions.workerSrc =
  'https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.worker.min.js';

const fileInput = document.getElementById('fileInput');
const canvas    = document.getElementById('canvas');
const ctx       = canvas.getContext('2d');
const navPrev   = document.getElementById('navPrev');
const navNext   = document.getElementById('navNext');
const pageInput = document.getElementById('pageInput');
const pageCount = document.getElementById('pageCount');
const zoomIn    = document.getElementById('zoomIn');
const zoomOut   = document.getElementById('zoomOut');
const zoomLabel = document.getElementById('zoomLabel');
const empty     = document.getElementById('empty');
const viewer    = document.getElementById('viewer');
const pageWrap  = document.getElementById('pageWrap');
const textLayer = document.getElementById('textLayer');
const txtView   = document.getElementById('txtView');
const speakBtn  = document.getElementById('speak');
const voiceSel  = document.getElementById('voice');
const rate      = document.getElementById('rate');
const rateLabel = document.getElementById('rateLabel');
const rateMult  = document.getElementById('rateMult');
const autoAdv   = document.getElementById('autoAdvance');
const status    = document.getElementById('status');

let pdfDoc = null;
let mode = 'pdf';       // 'pdf' | 'txt'
let txtPages = [];      // array of page strings when mode === 'txt'
let txtFont = 18;       // txt font size (px), driven by zoom buttons
let pageNum = 1;
let scale = 1.8;
let rendering = false;
let pendingPage = null;
let lastRendered = 0;   // page number whose canvas+text layer are ready

// per-page text model built during render, reused for speech + highlight
let pageText = '';          // full spoken string for current page
let spans = [];             // [{el, start, end}] char range each span covers

const synth = window.speechSynthesis;
let speaking = false;
let paused = false;
let voices = [];
let curSpanIdx = -1;
let speakGen = 0;   // bumped on every stop/restart; stale closures bail
let curChar = 0;       // char offset where current chunk started (resume point)
let wpmEma = null;     // measured words-per-minute, smoothed over spoken chunks
let wpmRate = 1;       // rate multiplier at which wpmEma was measured
let hlTimer = null;    // interval sweeping the highlight when no boundary events
function clearHlTimer() { if (hlTimer) { clearInterval(hlTimer); hlTimer = null; } }

async function renderPage(num) {
  if (!pdfDoc) return;
  rendering = true;
  const page = await pdfDoc.getPage(num);
  const dpr = window.devicePixelRatio || 1;
  const viewport = page.getViewport({ scale });
  const w = Math.floor(viewport.width), h = Math.floor(viewport.height);
  canvas.width  = Math.floor(viewport.width  * dpr);
  canvas.height = Math.floor(viewport.height * dpr);
  canvas.style.width  = w + 'px';
  canvas.style.height = h + 'px';
  pageWrap.style.width  = w + 'px';
  pageWrap.style.height = h + 'px';
  textLayer.style.width  = w + 'px';
  textLayer.style.height = h + 'px';
  await page.render({
    canvasContext: ctx,
    viewport,
    transform: dpr !== 1 ? [dpr, 0, 0, dpr, 0, 0] : null
  }).promise;
  await buildTextLayer(page, viewport);
  lastRendered = num;
  rendering = false;
  if (pendingPage !== null) {
    const p = pendingPage; pendingPage = null;
    renderPage(p);
  }
}

// Build absolutely-positioned spans over the canvas AND the spoken string.
// Each span records the char range it occupies in pageText for highlight sync.
async function buildTextLayer(page, viewport) {
  textLayer.innerHTML = '';
  spans = [];
  curSpanIdx = -1;
  const content = await page.getTextContent();
  let text = '';
  const toScale = [];
  for (const item of content.items) {
    const str = item.str;
    if (!str) { if (item.hasEOL) text += ' '; continue; }
    const tx = pdfjsLib.Util.transform(viewport.transform, item.transform);
    const fontH = Math.hypot(tx[2], tx[3]);
    const el = document.createElement('span');
    el.textContent = str;
    el.style.left = tx[4] + 'px';
    el.style.top  = (tx[5] - fontH) + 'px';
    el.style.fontSize = fontH + 'px';
    el.style.fontFamily = 'sans-serif';
    const start = text.length;
    text += str;
    spans.push({ el, start, end: text.length });
    text += ' ';
    textLayer.appendChild(el);
    if (item.width) toScale.push([el, item.width * viewport.scale]);
  }
  pageText = text;
  // one measurement pass: squeeze each span to its PDF-measured width
  for (const [el, wpx] of toScale) {
    const natural = el.getBoundingClientRect().width;
    if (natural > 0) el.style.transform = 'scaleX(' + (wpx / natural) + ')';
  }
}

function clearHighlight() {
  if (curSpanIdx >= 0 && spans[curSpanIdx]) spans[curSpanIdx].el.classList.remove('reading');
  curSpanIdx = -1;
}

function highlightAt(charIndex) {
  // find span whose range contains charIndex
  let idx = -1;
  for (let i = 0; i < spans.length; i++) {
    if (charIndex >= spans[i].start && charIndex < spans[i].end) { idx = i; break; }
    if (spans[i].start > charIndex) { idx = i; break; }
  }
  if (idx === curSpanIdx || idx < 0) return;
  if (curSpanIdx >= 0 && spans[curSpanIdx]) spans[curSpanIdx].el.classList.remove('reading');
  curSpanIdx = idx;
  const el = spans[idx].el;
  el.classList.add('reading');
  // keep reading word in view
  const r = el.getBoundingClientRect();
  const vr = viewer.getBoundingClientRect();
  if (r.top < vr.top + 40 || r.bottom > vr.bottom - 40) {
    viewer.scrollTop += (r.top - vr.top) - vr.height / 3;
  }
}

// Render a plain-text page: build visible word spans + the spoken string,
// reusing the same spans/pageText model the PDF text layer uses so speech
// and highlight logic work unchanged.
function renderTxtPage(num) {
  txtView.innerHTML = '';
  spans = [];
  curSpanIdx = -1;
  const page = txtPages[num - 1] || '';
  let text = '';
  // split keeping whitespace so original layout + char offsets are preserved
  for (const part of page.split(/(\s+)/)) {
    if (!part) continue;
    if (/^\s+$/.test(part)) {
      txtView.appendChild(document.createTextNode(part));
      text += part;
    } else {
      const el = document.createElement('span');
      el.textContent = part;
      const start = text.length;
      text += part;
      spans.push({ el, start, end: text.length });
      txtView.appendChild(el);
    }
  }
  pageText = text;
  txtView.style.fontSize = txtFont + 'px';
  lastRendered = num;
}

function queueRender(num) {
  if (mode === 'txt') { renderTxtPage(num); return; }
  if (rendering) pendingPage = num;
  else renderPage(num);
}

function goTo(num, keepSpeaking) {
  if (!pdfDoc) return;
  num = Math.max(1, Math.min(pdfDoc.numPages, num));
  pageNum = num;
  pageInput.value = num;
  navPrev.disabled = num <= 1;
  navNext.disabled = num >= pdfDoc.numPages;
  viewer.scrollTop = 0;
  queueRender(num);
  if (!keepSpeaking) stopSpeak();
}

function loadVoices() {
  voices = synth.getVoices();
  if (!voices.length) return;
  const prev = voiceSel.value;
  voiceSel.innerHTML = '';
  voices.forEach((v, i) => {
    const o = document.createElement('option');
    o.value = i;
    o.textContent = v.name + (v.lang ? ' (' + v.lang + ')' : '');
    voiceSel.appendChild(o);
  });
  // default: first English voice
  const en = voices.findIndex(v => /^en/i.test(v.lang));
  voiceSel.value = prev || (en >= 0 ? en : 0);
}
loadVoices();
synth.onvoiceschanged = loadVoices;

// split pageText into sentence chunks with their base char offset.
// Chunking avoids Chrome's ~15s single-utterance cutoff and keeps
// boundary offsets small/accurate.
// PDF: a newline ends a chunk (pdf.js joins with spaces, so \n is rare/real).
// TXT: hard-wrapped lines carry mid-sentence \n, so a lone newline is NOT a
// break — only .!? and blank-line paragraph breaks split a chunk.
function chunkPage() {
  const t = pageText;
  const isTxt = mode === 'txt';
  const chunks = [];
  let start = 0;
  const push = (end) => {
    const s = t.slice(start, end);
    if (s.trim()) chunks.push({ text: s, base: start });
    start = end;
  };
  let i = 0;
  while (i < t.length) {
    const ch = t[i];
    if (ch === '.' || ch === '!' || ch === '?' || (!isTxt && ch === '\n')) {
      let j = i + 1;
      while (j < t.length && '.!?'.indexOf(t[j]) >= 0) j++; // eat "?!" runs
      push(j); i = j; continue;
    }
    if (isTxt && ch === '\n') {   // paragraph break = 2+ newlines in a ws run
      let j = i + 1, nl = 1;
      while (j < t.length && /\s/.test(t[j])) { if (t[j] === '\n') nl++; j++; }
      if (nl >= 2) { push(j); i = j; continue; }
      i++; continue;             // lone newline -> stays inside the chunk
    }
    i++;
  }
  if (start < t.length) push(t.length);
  if (!chunks.length && t.trim()) chunks.push({ text: t, base: 0 });
  return chunks;
}

// advance to next page, wait for its render, then resume speaking
function advanceAndSpeak(gen) {
  goTo(pageNum + 1, true);
  const target = pageNum;
  const wait = () => {
    if (gen !== speakGen) return;
    if (lastRendered === target && !rendering) speakPage(gen);
    else setTimeout(wait, 50);
  };
  wait();
}

function speakPage(gen, startChar) {
  if (gen !== speakGen) return;
  let chunks = chunkPage();
  // start from a specific char offset (word click / rate / voice resume):
  // drop chunks before it, trim the one that contains it
  if (startChar) {
    chunks = chunks.filter(c => c.base + c.text.length > startChar);
    if (chunks.length && startChar > chunks[0].base) {
      const c0 = chunks[0];
      chunks = chunks.slice();
      chunks[0] = { text: c0.text.slice(startChar - c0.base), base: startChar };
    }
  }
  if (!chunks.length) {
    // no text layer (scanned/image page) -> skip if auto
    if (autoAdv.checked && pageNum < pdfDoc.numPages) {
      advanceAndSpeak(gen);
    } else { stopSpeak(); }
    return;
  }
  const v = voices[parseInt(voiceSel.value, 10)];
  let i = 0;
  const speakChunk = () => {
    if (gen !== speakGen) return;
    if (i >= chunks.length) {
      // page done -> advance or stop
      if (autoAdv.checked && pageNum < pdfDoc.numPages) {
        advanceAndSpeak(gen);
      } else {
        stopSpeak();
      }
      return;
    }
    const c = chunks[i++];
    curChar = c.base;
    const words = (c.text.match(/\S+/g) || []).length;
    const totalChars = c.text.length;
    // swap newlines/tabs for spaces so engines don't pause on them;
    // 1:1 replace keeps length == totalChars, so boundary offsets align
    const u = new SpeechSynthesisUtterance(c.text.replace(/[\n\t]/g, ' '));
    if (v) u.voice = v;
    const r = parseFloat(rate.value);
    u.rate = r;
    let t0 = 0;
    let boundaryLive = false;   // true once a real onboundary fires (Chrome)

    u.onstart = () => {
      t0 = performance.now();
      highlightAt(c.base);
      // timer-driven highlight: sweep a virtual char position through the
      // sentence at the measured pace. Firefox fires no onboundary, so this
      // keeps the line highlight moving; Chrome's real boundaries take over.
      const estDur = (words / Math.max(60, predictWpm(r))) * 60000; // ms
      const charsPerMs = totalChars / Math.max(1, estDur);
      clearHlTimer();
      hlTimer = setInterval(() => {
        if (gen !== speakGen || boundaryLive) { clearHlTimer(); return; }
        if (paused) { t0 += 60; return; }   // freeze while paused
        const ci = Math.min(totalChars, (performance.now() - t0) * charsPerMs);
        highlightAt(c.base + ci);
      }, 60);
    };
    u.onboundary = (e) => {
      if (gen !== speakGen) return;
      boundaryLive = true;   // real timings available; stop the estimator
      clearHlTimer();
      highlightAt(c.base + (e.charIndex || 0));
    };
    u.onend = () => {
      clearHlTimer();
      if (t0 && words >= 3) recordWpm(words, performance.now() - t0, r);
      if (gen === speakGen) speakChunk();
    };
    u.onerror = () => { clearHlTimer(); if (gen === speakGen) speakChunk(); };
    synth.speak(u);
  };
  speakChunk();
}

function startSpeak(startChar) {
  if (!pdfDoc) return;
  if (!voices.length) voices = synth.getVoices();
  if (!voices.length) {
    status.textContent = 'No TTS voices found. Linux: install speech-dispatcher + espeak-ng, or use Chrome.';
    return;
  }
  status.textContent = '';
  synth.cancel();
  speakGen++;
  speaking = true;
  paused = false;
  updateSpeakBtn();
  speakPage(speakGen, startChar || 0);
}

// click a word -> (re)start reading from that word
function wordClick(e) {
  const el = e.target.closest('span');
  if (!el) return;
  const sp = spans.find(s => s.el === el);
  if (sp) startSpeak(sp.start);
}
textLayer.addEventListener('click', wordClick);
txtView.addEventListener('click', wordClick);

function stopSpeak() {
  speaking = false;
  paused = false;
  speakGen++;   // invalidate any in-flight chunk chain
  clearHlTimer();
  synth.cancel();
  clearHighlight();
  updateSpeakBtn();
}

// one button: play when idle, pause while speaking, resume while paused.
// track paused ourselves — synth.paused is unreliable on some engines.
function updateSpeakBtn() {
  const playing = speaking && !paused;
  speakBtn.textContent = playing ? '❙❙' : '▶';
  speakBtn.classList.toggle('speaking', speaking);
}
function togglePlay() {
  if (!speaking) startSpeak();
  else if (paused) { synth.resume(); paused = false; updateSpeakBtn(); }
  else { synth.pause(); paused = true; updateSpeakBtn(); }
}

function enableControls() {
  pageNum = 1;
  pageInput.disabled = false;
  pageInput.max = pdfDoc.numPages;
  pageCount.textContent = '/ ' + pdfDoc.numPages;
  zoomIn.disabled = zoomOut.disabled = false;
  speakBtn.disabled = voiceSel.disabled = rate.disabled = autoAdv.disabled = false;
  empty.style.display = 'none';
  pageWrap.style.display = 'block';
}

async function loadPdf(data) {
  stopSpeak();
  mode = 'pdf';
  pdfDoc = await pdfjsLib.getDocument(data).promise;
  // pdf mode: show canvas + transparent text layer, hide txt view
  canvas.style.display = textLayer.style.display = 'block';
  txtView.style.display = 'none';
  zoomLabel.textContent = Math.round(scale / 1.2 * 100) + '%';
  enableControls();
  goTo(1);
}

// paginate raw text so pages stay a sensible reading length
function paginateTxt(text, perPage = 2500) {
  const pages = [];
  // prefer breaking on blank lines (paragraphs), fall back to size
  const paras = text.split(/\n{2,}/);
  let buf = '';
  for (const p of paras) {
    if (buf && buf.length + p.length > perPage) { pages.push(buf); buf = ''; }
    buf += (buf ? '\n\n' : '') + p;
    while (buf.length > perPage) {   // single huge paragraph -> hard split
      pages.push(buf.slice(0, perPage));
      buf = buf.slice(perPage);
    }
  }
  if (buf.trim()) pages.push(buf);
  return pages.length ? pages : [''];
}

function loadTxt(text) {
  stopSpeak();
  mode = 'txt';
  txtPages = paginateTxt(text);
  pdfDoc = { numPages: txtPages.length };   // fake doc: only numPages is read in txt mode
  // txt mode: show visible text view, hide canvas + pdf text layer
  canvas.style.display = textLayer.style.display = 'none';
  txtView.style.display = 'block';
  pageWrap.style.width = '';
  pageWrap.style.height = '';
  zoomLabel.textContent = Math.round(txtFont / 18 * 100) + '%';
  enableControls();
  goTo(1);
}

fileInput.addEventListener('change', (e) => {
  const file = e.target.files[0];
  if (!file) return;
  const isTxt = file.type === 'text/plain' || /\.txt$/i.test(file.name);
  if (isTxt) {
    file.text().then(loadTxt).catch(() => {
      status.textContent = 'Could not read text file.';
    });
  } else {
    loadPdf(URL.createObjectURL(file));
  }
});

navPrev.addEventListener('click', () => goTo(pageNum - 1));
navNext.addEventListener('click', () => goTo(pageNum + 1));
pageInput.addEventListener('change', () => goTo(parseInt(pageInput.value, 10) || 1));

function zoomTxt(delta) {
  txtFont = Math.max(10, Math.min(40, txtFont + delta));
  txtView.style.fontSize = txtFont + 'px';
  zoomLabel.textContent = Math.round(txtFont / 18 * 100) + '%';
}
zoomIn.addEventListener('click', () => {
  if (mode === 'txt') { zoomTxt(2); return; }
  scale = Math.min(4, scale + 0.2);
  zoomLabel.textContent = Math.round(scale / 1.2 * 100) + '%';
  queueRender(pageNum);
});
zoomOut.addEventListener('click', () => {
  if (mode === 'txt') { zoomTxt(-2); return; }
  scale = Math.max(0.4, scale - 0.2);
  zoomLabel.textContent = Math.round(scale / 1.2 * 100) + '%';
  queueRender(pageNum);
});

speakBtn.addEventListener('click', togglePlay);
const BASE_WPM = 175;   // fallback estimate before we have a measurement
function setWpmLabel(n) { rateLabel.childNodes[0].nodeValue = Math.round(n) + ' wpm '; }

// measured wpm from real speech; EMA smooths chunk-to-chunk jitter
function recordWpm(words, ms, r) {
  if (ms <= 0) return;
  const wpm = words / (ms / 60000);
  wpmEma = wpmEma == null ? wpm : wpmEma * 0.7 + wpm * 0.3;
  wpmRate = r;
  setWpmLabel(wpmEma);
}

// predicted wpm at a given slider rate: scale the measured voice speed,
// or fall back to the rough baseline until we've measured this voice
function predictWpm(r) {
  return wpmEma != null ? wpmEma * (r / wpmRate) : r * BASE_WPM;
}

function setMultLabel(r) {
  rateMult.textContent = (Number.isInteger(r) ? r : r.toFixed(1)) + 'x';
}
rate.addEventListener('input', () => {
  const r = parseFloat(rate.value);
  setWpmLabel(predictWpm(r));
  setMultLabel(r);
});

voiceSel.addEventListener('change', () => {
  wpmEma = null; wpmRate = 1;               // new voice -> re-measure speed
  setWpmLabel(predictWpm(parseFloat(rate.value)));
  if (speaking) {                            // apply new voice from current spot
    const resumeChar = curChar;
    synth.cancel();
    speakGen++;
    speakPage(speakGen, resumeChar);
  }
});
// apply new rate WITHOUT losing place: resume from current sentence chunk
rate.addEventListener('change', () => {
  if (speaking) {
    const resumeChar = curChar;
    synth.cancel();
    speakGen++;
    speakPage(speakGen, resumeChar);
  }
});

document.addEventListener('keydown', (e) => {
  if (e.target === pageInput) return;
  if (e.key === 'ArrowRight' || e.key === 'PageDown') goTo(pageNum + 1);
  if (e.key === 'ArrowLeft'  || e.key === 'PageUp')   goTo(pageNum - 1);
  if (e.key === ' ') { e.preventDefault(); togglePlay(); }
});

// stop speech if tab closed/reloaded (some browsers keep speaking)
window.addEventListener('beforeunload', () => synth.cancel());
