// ============================================================
// POLAR BATTLESHIP - Canvas/JS port
// ============================================================

// ---------- Angles ----------
// Generate all special angles: multiples of pi/6, pi/4, pi/3, pi/2 in [0, 2pi)
function gcd(a, b) { return b ? gcd(b, a % b) : a; }
function makeFraction(num, den) {
  const g = gcd(Math.abs(num), den);
  return { num: num / g, den: den / g };
}
function fracEqual(a, b) { return a.num === b.num && a.den === b.den; }
function fracKey(f) { return `${f.num}/${f.den}`; }
function fracValue(f) { return f.num / f.den; }

const angleFractionMap = new Map();
[6, 4, 3, 2].forEach(denom => {
  for (let k = 0; k < 2 * denom; k++) {
    const f = makeFraction(k, denom);
    angleFractionMap.set(fracKey(f), f);
  }
});
const angleFractions = [...angleFractionMap.values()].sort(
  (a, b) => fracValue(a) - fracValue(b)
);
const specialAngles = angleFractions.map(f => fracValue(f) * Math.PI);
const N_ANG = specialAngles.length;

function piLabel(frac) {
  if (frac.num === 0) return '0';
  const numStr = frac.num === 1 ? 'π' : `${frac.num}π`;
  return frac.den === 1 ? numStr : `${numStr}/${frac.den}`;
}

// ---------- Constants ----------
const R_MAX = 5;
const R_MIN = 0;
const SHIP_SIZES = [2, 3, 4];
const SHIP_NAMES = ['DESTROYER', 'BATTLESHIP', 'CARRIER'];
const SHIP_COLORS = ['#5dffc4', '#ffb84d', '#7ec8ff'];  // phosphor green, amber, sonar blue
const NUM_SHIPS = SHIP_SIZES.length;

// ---------- Adjacency / placement helpers ----------
function canonicalCell(point) {
  const [ai, r] = point;
  return r === 0 ? [-1, 0] : [ai, r];
}
function cellKey(point) {
  const c = canonicalCell(point);
  return `${c[0]},${c[1]}`;
}
function isAdjacent(p, q) {
  const [aiP, rP] = p;
  const [aiQ, rQ] = q;
  if (rP === 0 && rQ === 1) return true;
  if (rQ === 0 && rP === 1) return true;
  if (rP === 0 && rQ === 0) return false;
  const sameAngle = (aiP === aiQ) && (Math.abs(rP - rQ) === 1);
  const angDiff = Math.min(
    ((aiP - aiQ) % N_ANG + N_ANG) % N_ANG,
    ((aiQ - aiP) % N_ANG + N_ANG) % N_ANG
  );
  const sameRadius = (rP === rQ) && (angDiff === 1);
  return sameAngle || sameRadius;
}
function neighborsCanonical(canon) {
  const [ai, r] = canon;
  const out = [];
  if (r === 0) {
    for (let a = 0; a < N_ANG; a++) out.push([a, 1]);
  } else {
    if (r - 1 === 0) out.push([-1, 0]);
    else if (r - 1 >= 1) out.push([ai, r - 1]);
    if (r + 1 <= R_MAX) out.push([ai, r + 1]);
    out.push([((ai - 1) % N_ANG + N_ANG) % N_ANG, r]);
    out.push([(ai + 1) % N_ANG, r]);
  }
  return out;
}

// ---------- Random ship placement (for CPU) ----------
function placeOne(size, usedKeys, attempts = 400) {
  for (let t = 0; t < attempts; t++) {
    const orient = Math.random() < 0.5 ? 'arc' : 'radial';
    let ship;
    if (orient === 'arc') {
      const r = 1 + Math.floor(Math.random() * R_MAX);
      const startAi = Math.floor(Math.random() * N_ANG);
      const dir = Math.random() < 0.5 ? 1 : -1;
      ship = [];
      for (let k = 0; k < size; k++) {
        ship.push([((startAi + dir * k) % N_ANG + N_ANG) % N_ANG, r]);
      }
    } else {
      const ai = Math.floor(Math.random() * N_ANG);
      if (size > (R_MAX - R_MIN + 1)) continue;
      const dir = Math.random() < 0.5 ? 1 : -1;
      let startR;
      if (dir === 1) startR = R_MIN + Math.floor(Math.random() * (R_MAX - size + 2));
      else           startR = R_MIN + size - 1 + Math.floor(Math.random() * (R_MAX - size + 2));
      ship = [];
      let bad = false;
      for (let k = 0; k < size; k++) {
        const rr = startR + dir * k;
        if (rr < R_MIN || rr > R_MAX) { bad = true; break; }
        ship.push([ai, rr]);
      }
      if (bad) continue;
    }
    const keys = ship.map(cellKey);
    if (keys.some(k => usedKeys.has(k))) continue;
    if (new Set(keys).size !== size) continue;
    return ship;
  }
  return null;
}
function randomPlaceShips(sizes, maxAttempts = 2000) {
  for (let t = 0; t < maxAttempts; t++) {
    const used = new Set();
    const placements = [];
    let ok = true;
    for (const size of sizes) {
      const s = placeOne(size, used);
      if (!s) { ok = false; break; }
      placements.push(s);
      s.forEach(c => used.add(cellKey(c)));
    }
    if (ok) return placements;
  }
  throw new Error('Could not place CPU ships');
}

// ---------- Game state ----------
const state = {
  phase: 'place',  // 'place' | 'guess' | 'done'
  shipsPlayer: [[], [], []],
  currentShip: 0,
  shipsCpu: [],
  cpuHits: new Set(),       // keys of cells player has hit on CPU board
  cpuMisses: new Set(),
  cpuHitPoints: [],         // raw [ai, r] for drawing
  cpuMissPoints: [],
  playerHits: new Set(),    // keys where CPU has hit player ships
  playerMisses: new Set(),
  playerHitPoints: [],
  playerMissPoints: [],
  cpuTargetsQueue: [],
  cpuHitStreak: [],
  selectedRadius: 1,
  selectedAngleIdx: 0,
  sonarAngleDeg: 0,
  prevSonarAngleDeg: 0,    // last frame's sweep angle, for crossing detection
  pings: [],               // active hit-pings: { ai, r, t } where t is elapsed seconds
};

// ---------- Canvas setup ----------
const playerCanvas = document.getElementById('player-canvas');
const cpuCanvas = document.getElementById('cpu-canvas');
const pctx = playerCanvas.getContext('2d');
const cctx = cpuCanvas.getContext('2d');

// Ensure a canvas's backing store matches its current displayed CSS size.
// Safe to call every frame: it only does work when the size actually changed
// (e.g. after the placement->guessing layout switch, or a window resize).
// Returns the CSS-pixel size to draw with.
function syncCanvas(canvas, ctx) {
  const dpr = window.devicePixelRatio || 1;
  const cssSize = canvas.clientWidth;
  if (cssSize === 0) return 0;            // not laid out yet; skip this frame
  const wantW = Math.round(cssSize * dpr);
  if (canvas.width !== wantW) {
    // Setting canvas.width resets the context transform to identity.
    canvas.width = wantW;
    canvas.height = wantW;
  }
  // Re-apply the dpr transform every call so drawing uses CSS-pixel coords.
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  return cssSize;
}

let CANVAS_SIZE = syncCanvas(playerCanvas, pctx);
syncCanvas(cpuCanvas, cctx);
window.addEventListener('resize', () => {
  CANVAS_SIZE = syncCanvas(playerCanvas, pctx);
  syncCanvas(cpuCanvas, cctx);
  redrawAll();
});

function polarToXY(ai, r, size) {
  // We rotate so theta=0 points right, going counter-clockwise (standard math)
  const cx = size / 2;
  const cy = size / 2;
  const maxR = (size / 2) - 30; // padding for labels
  const theta = specialAngles[ai];
  const rr = (r / R_MAX) * maxR;
  return {
    x: cx + rr * Math.cos(theta),
    y: cy - rr * Math.sin(theta),
    cx, cy, maxR
  };
}

// ---------- Grid drawing ----------
function drawGrid(ctx, size, isCpu) {
  const cx = size / 2, cy = size / 2;
  const maxR = (size / 2) - 30;

  // Radial circles
  ctx.strokeStyle = 'rgba(45, 90, 110, 0.5)';
  ctx.lineWidth = 1;
  for (let r = 1; r <= R_MAX; r++) {
    ctx.beginPath();
    ctx.arc(cx, cy, (r / R_MAX) * maxR, 0, Math.PI * 2);
    ctx.stroke();
  }

  // Angular spokes
  ctx.strokeStyle = 'rgba(45, 90, 110, 0.35)';
  for (let i = 0; i < N_ANG; i++) {
    const theta = specialAngles[i];
    ctx.beginPath();
    ctx.moveTo(cx, cy);
    ctx.lineTo(cx + maxR * Math.cos(theta), cy - maxR * Math.sin(theta));
    ctx.stroke();
  }

  // Angle labels
  ctx.fillStyle = '#9ad6bf';
  ctx.font = 'bold 12px "Share Tech Mono"';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.shadowColor = 'rgba(93, 255, 196, 0.4)';
  ctx.shadowBlur = 4;
  for (let i = 0; i < N_ANG; i++) {
    const theta = specialAngles[i];
    const lblR = maxR + 16;
    const lx = cx + lblR * Math.cos(theta);
    const ly = cy - lblR * Math.sin(theta);
    ctx.fillText(piLabel(angleFractions[i]), lx, ly);
  }
  ctx.shadowBlur = 0;

  // Radius labels (along theta=0 axis)
  ctx.fillStyle = '#3a5a68';
  ctx.font = '10px "Share Tech Mono"';
  ctx.textAlign = 'left';
  for (let r = 1; r <= R_MAX; r++) {
    ctx.fillText(r.toString(), cx + (r / R_MAX) * maxR + 3, cy - 6);
  }

  // Intersection dots
  ctx.fillStyle = isCpu ? 'rgba(125, 200, 255, 0.25)' : 'rgba(93, 255, 196, 0.35)';
  for (let i = 0; i < N_ANG; i++) {
    for (let r = 1; r <= R_MAX; r++) {
      const { x, y } = polarToXY(i, r, size);
      ctx.beginPath();
      ctx.arc(x, y, 2, 0, Math.PI * 2);
      ctx.fill();
    }
  }
  // Origin dot
  ctx.beginPath();
  ctx.arc(cx, cy, 3, 0, Math.PI * 2);
  ctx.fill();
}

// ---------- Sonar sweep ----------
function drawSonarSweep(ctx, size) {
  const cx = size / 2, cy = size / 2;
  const maxR = (size / 2) - 30;

  // Faint blue overlay disc
  ctx.fillStyle = 'rgba(125, 200, 255, 0.05)';
  ctx.beginPath();
  ctx.arc(cx, cy, maxR, 0, Math.PI * 2);
  ctx.fill();

  // Rotating wedge with fading tail
  const leadDeg = state.sonarAngleDeg;
  const widthDeg = 30;
  const nBands = 14;
  const bandDeg = widthDeg / nBands;

  for (let i = 0; i < nBands; i++) {
    // Canvas angles go clockwise from 3 o'clock; we want CCW from 3 o'clock.
    // So negate the degrees.
    const aLead = -(leadDeg - i * bandDeg) * Math.PI / 180;
    const aTrail = -(leadDeg - (i + 1) * bandDeg) * Math.PI / 180;
    const alpha = 0.45 * (1 - i / nBands) + 0.04;
    ctx.fillStyle = `rgba(125, 200, 255, ${alpha})`;
    ctx.beginPath();
    ctx.moveTo(cx, cy);
    // arc goes from aLead to aTrail (note negation flips direction)
    ctx.arc(cx, cy, maxR, Math.min(aLead, aTrail), Math.max(aLead, aTrail));
    ctx.closePath();
    ctx.fill();
  }

  // Bright leading edge line
  const aLeadRad = -leadDeg * Math.PI / 180;
  ctx.strokeStyle = 'rgba(207, 232, 255, 0.85)';
  ctx.lineWidth = 1.5;
  ctx.shadowColor = '#7ec8ff';
  ctx.shadowBlur = 8;
  ctx.beginPath();
  ctx.moveTo(cx, cy);
  ctx.lineTo(cx + maxR * Math.cos(aLeadRad), cy + maxR * Math.sin(aLeadRad));
  ctx.stroke();
  ctx.shadowBlur = 0;
}

// ---------- Hit-target sonar pings ----------
const PING_DURATION = 0.9;  // seconds for a ping to expand and fade

// True if the sweep's leading edge moved across `targetDeg` this frame.
// All values are degrees in [0, 360), sweep advances by a positive step.
function sweepCrossed(prevDeg, curDeg, targetDeg) {
  // Normalize so we measure forward travel from prevDeg.
  const span = ((curDeg - prevDeg) % 360 + 360) % 360;
  const offset = ((targetDeg - prevDeg) % 360 + 360) % 360;
  return offset <= span;
}

// Each frame: if the sweep crossed the bearing of an already-hit CPU cell,
// start a fresh ping there.
function updatePings(dt) {
  // Advance / retire existing pings
  for (const p of state.pings) p.t += dt;
  state.pings = state.pings.filter(p => p.t < PING_DURATION);

  // Detect new crossings over hit cells
  for (const [ai, r] of state.cpuHitPoints) {
    const bearingDeg = (specialAngles[ai] * 180 / Math.PI) % 360;
    if (sweepCrossed(state.prevSonarAngleDeg, state.sonarAngleDeg, bearingDeg)) {
      // Refresh the ping for this cell (replace any in-flight one)
      state.pings = state.pings.filter(p => !(p.ai === ai && p.r === r));
      state.pings.push({ ai, r, t: 0 });
    }
  }
}

function drawPings(ctx, size) {
  for (const p of state.pings) {
    const { x, y } = polarToXY(p.ai, p.r, size);
    const prog = p.t / PING_DURATION;          // 0 -> 1
    const ringR = 6 + prog * 26;               // expanding radius
    const alpha = (1 - prog) * 0.85;           // fading out

    // Expanding ring
    ctx.strokeStyle = `rgba(255, 77, 94, ${alpha})`;
    ctx.lineWidth = 2.5 * (1 - prog) + 0.5;
    ctx.shadowColor = '#ff4d5e';
    ctx.shadowBlur = 16 * (1 - prog);
    ctx.beginPath();
    ctx.arc(x, y, ringR, 0, Math.PI * 2);
    ctx.stroke();

    // Bright core flare, strongest at the start of the ping
    const coreAlpha = (1 - prog) * (1 - prog) * 0.9;
    ctx.fillStyle = `rgba(255, 200, 205, ${coreAlpha})`;
    ctx.beginPath();
    ctx.arc(x, y, 4 + (1 - prog) * 5, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.shadowBlur = 0;
}

// ---------- Ship drawing (player only) ----------
function sortShipAlongLine(ship) {
  if (ship.length < 2) return ship.slice();
  const nonOrigin = ship.filter(([_, r]) => r !== 0);
  const hasOrigin = nonOrigin.length < ship.length;
  if (nonOrigin.length === 0) return ship.slice();
  const radii = new Set(nonOrigin.map(([_, r]) => r));
  const angles = new Set(nonOrigin.map(([a]) => a));
  if (radii.size === 1) {
    const rVal = [...radii][0];
    let ais = nonOrigin.map(([a]) => a).sort((a, b) => a - b);
    if (ais.length > 1) {
      const gaps = ais.map((a, i) => {
        const next = ais[(i + 1) % ais.length];
        return ((next - a) % N_ANG + N_ANG) % N_ANG;
      });
      let maxGapIdx = 0;
      for (let i = 1; i < gaps.length; i++) {
        if (gaps[i] > gaps[maxGapIdx]) maxGapIdx = i;
      }
      ais = ais.slice(maxGapIdx + 1).concat(ais.slice(0, maxGapIdx + 1));
    }
    return ais.map(a => [a, rVal]);
  }
  if (angles.size === 1) {
    const aVal = [...angles][0];
    const sorted = nonOrigin.slice().sort((a, b) => a[1] - b[1]);
    return hasOrigin ? [[aVal, 0], ...sorted] : sorted;
  }
  return ship.slice();
}

function drawShip(ctx, size, ship, color) {
  if (ship.length === 0) return;
  const sorted = sortShipAlongLine(ship);

  ctx.strokeStyle = color;
  ctx.lineWidth = 3;
  ctx.shadowColor = color;
  ctx.shadowBlur = 10;

  for (let i = 0; i < sorted.length - 1; i++) {
    const [a1, r1] = sorted[i];
    const [a2, r2] = sorted[i + 1];

    if (r1 === 0 || r2 === 0) {
      // Radial segment through origin
      const p1 = polarToXY(a1, r1, size);
      const p2 = polarToXY(a2, r2, size);
      ctx.beginPath();
      ctx.moveTo(p1.x, p1.y);
      ctx.lineTo(p2.x, p2.y);
      ctx.stroke();
    } else if (r1 === r2) {
      // Arc segment along circle of radius r1
      const { cx, cy, maxR } = polarToXY(a1, r1, size);
      const radius = (r1 / R_MAX) * maxR;
      // Determine sweep direction (shorter way)
      const t1 = specialAngles[a1];
      const t2 = specialAngles[a2];
      const fwd = ((a2 - a1) % N_ANG + N_ANG) % N_ANG;
      const bwd = ((a1 - a2) % N_ANG + N_ANG) % N_ANG;
      ctx.beginPath();
      // Canvas angles are clockwise; our theta is CCW. Negate.
      if (fwd <= bwd) {
        ctx.arc(cx, cy, radius, -t1, -t2, true);  // anticlockwise=true in canvas terms
      } else {
        ctx.arc(cx, cy, radius, -t1, -t2, false);
      }
      ctx.stroke();
    } else {
      // Straight radial line (same angle)
      const p1 = polarToXY(a1, r1, size);
      const p2 = polarToXY(a2, r2, size);
      ctx.beginPath();
      ctx.moveTo(p1.x, p1.y);
      ctx.lineTo(p2.x, p2.y);
      ctx.stroke();
    }
  }
  ctx.shadowBlur = 0;

  // Square nodes at each ship point
  ctx.fillStyle = color;
  ctx.strokeStyle = '#000';
  ctx.lineWidth = 1.5;
  for (const [ai, r] of sorted) {
    const { x, y } = polarToXY(ai, r, size);
    ctx.fillRect(x - 7, y - 7, 14, 14);
    ctx.strokeRect(x - 7, y - 7, 14, 14);
  }
}

// ---------- Hit/miss markers ----------
function drawHitsMisses(ctx, size, hits, misses) {
  // Misses: dim X
  ctx.strokeStyle = '#6a8a98';
  ctx.lineWidth = 2;
  for (const [ai, r] of misses) {
    const { x, y } = polarToXY(ai, r, size);
    ctx.beginPath();
    ctx.moveTo(x - 7, y - 7); ctx.lineTo(x + 7, y + 7);
    ctx.moveTo(x + 7, y - 7); ctx.lineTo(x - 7, y + 7);
    ctx.stroke();
  }
  // Hits: red glowing star
  ctx.fillStyle = '#ff4d5e';
  ctx.shadowColor = '#ff4d5e';
  ctx.shadowBlur = 14;
  for (const [ai, r] of hits) {
    const { x, y } = polarToXY(ai, r, size);
    drawStar(ctx, x, y, 5, 9, 4);
    ctx.fill();
  }
  ctx.shadowBlur = 0;
}
function drawStar(ctx, cx, cy, spikes, outerR, innerR) {
  ctx.beginPath();
  let rot = -Math.PI / 2;
  const step = Math.PI / spikes;
  ctx.moveTo(cx, cy - outerR);
  for (let i = 0; i < spikes; i++) {
    let x = cx + Math.cos(rot) * outerR;
    let y = cy + Math.sin(rot) * outerR;
    ctx.lineTo(x, y);
    rot += step;
    x = cx + Math.cos(rot) * innerR;
    y = cy + Math.sin(rot) * innerR;
    ctx.lineTo(x, y);
    rot += step;
  }
  ctx.lineTo(cx, cy - outerR);
  ctx.closePath();
}

// ---------- Redraw ----------
function redrawPlayer() {
  const size = syncCanvas(playerCanvas, pctx);
  if (size === 0) return;            // not laid out yet
  pctx.clearRect(0, 0, size, size);
  drawGrid(pctx, size, false);
  state.shipsPlayer.forEach((ship, idx) => {
    drawShip(pctx, size, ship, SHIP_COLORS[idx]);
  });
  drawHitsMisses(pctx, size, state.playerHitPoints, state.playerMissPoints);
}
function redrawCpu() {
  const size = syncCanvas(cpuCanvas, cctx);
  if (size === 0) return;            // not laid out yet (e.g. hidden in placement)
  cctx.clearRect(0, 0, size, size);
  drawGrid(cctx, size, true);
  drawSonarSweep(cctx, size);
  drawHitsMisses(cctx, size, state.cpuHitPoints, state.cpuMissPoints);
  drawPings(cctx, size);
}
function redrawAll() { redrawPlayer(); redrawCpu(); }

// ---------- Sonar animation loop ----------
let lastFrame = performance.now();
const SONAR_DEG_PER_SEC = 36; // one rev per 10 seconds
function animate(now) {
  // Clamp dt: the very first frame (or a backgrounded tab) can produce a
  // huge gap since lastFrame was set at load time. An unclamped dt makes the
  // sweep angle jump hundreds of degrees and land at a bogus value.
  let dt = (now - lastFrame) / 1000;
  if (dt > 0.1 || dt < 0) dt = 0.016;   // cap at ~one frame
  lastFrame = now;
  state.prevSonarAngleDeg = state.sonarAngleDeg;
  // Positive modulo: JS '%' keeps the dividend's sign, which can yield a
  // negative angle. ((x % 360) + 360) % 360 forces [0, 360).
  const raw = state.sonarAngleDeg + SONAR_DEG_PER_SEC * dt;
  state.sonarAngleDeg = ((raw % 360) + 360) % 360;
  updatePings(dt);
  redrawCpu();
  requestAnimationFrame(animate);
}
requestAnimationFrame(animate);

// ---------- Status bar / banner ----------
function setStatus(msg) {
  document.getElementById('status-text').textContent = msg;
}
function showBanner(text, variant, durationMs = 2200) {
  const el = document.getElementById('banner');
  el.className = `banner ${variant}`;
  el.innerHTML = `<span class="banner-text">${text}</span>`;
  if (durationMs > 0) {
    setTimeout(() => { el.className = 'banner hidden'; }, durationMs);
  }
}
function showEndBanner(text, variant) {
  const el = document.getElementById('banner');
  el.className = `banner ${variant}`;
  el.innerHTML = `
    <span class="banner-text">${text}</span>
    <button class="play-again-btn" id="play-again-btn">
      <span class="play-again-label">PLAY AGAIN</span>
    </button>
  `;
  document.getElementById('play-again-btn').addEventListener('click', resetGame);
}

// ---------- Fleet status display ----------
function renderFleets() {
  const playerEl = document.getElementById('player-fleet');
  const cpuEl = document.getElementById('cpu-fleet');
  playerEl.innerHTML = '';
  cpuEl.innerHTML = '';

  for (let i = 0; i < NUM_SHIPS; i++) {
    const ship = state.shipsPlayer[i];
    const sunk = ship.length === SHIP_SIZES[i] &&
      ship.every(c => state.playerHits.has(cellKey(c)));
    const div = document.createElement('div');
    div.className = `fleet-item ${sunk ? 'sunk' : 'alive'}`;
    div.innerHTML = `<span class="fleet-name">${SHIP_NAMES[i]}</span><span class="fleet-size">${SHIP_SIZES[i]} PTS</span>`;
    playerEl.appendChild(div);
  }
  for (let i = 0; i < NUM_SHIPS; i++) {
    const sunk = state.shipsCpu[i] && state.shipsCpu[i].every(c => state.cpuHits.has(cellKey(c)));
    const div = document.createElement('div');
    div.className = `fleet-item ${sunk ? 'sunk' : 'alive'}`;
    div.innerHTML = `<span class="fleet-name">${SHIP_NAMES[i]}</span><span class="fleet-size">${SHIP_SIZES[i]} PTS</span>`;
    cpuEl.appendChild(div);
  }
}

// ---------- Placement (click on player canvas) ----------
function clickToPolar(canvas, evt) {
  const rect = canvas.getBoundingClientRect();
  const size = canvas.clientWidth;
  const x = evt.clientX - rect.left;
  const y = evt.clientY - rect.top;
  const cx = size / 2, cy = size / 2;
  const maxR = (size / 2) - 30;
  const dx = x - cx, dy = cy - y;  // flip y so up is positive (math convention)
  const r_raw = Math.sqrt(dx * dx + dy * dy) / maxR * R_MAX;
  let theta = Math.atan2(dy, dx);
  if (theta < 0) theta += 2 * Math.PI;
  // Snap to nearest angle
  let bestI = 0, bestDiff = Infinity;
  for (let i = 0; i < N_ANG; i++) {
    const a = specialAngles[i];
    let d = Math.abs(a - theta);
    if (d > Math.PI) d = 2 * Math.PI - d;
    if (d < bestDiff) { bestDiff = d; bestI = i; }
  }
  const r = Math.max(R_MIN, Math.min(R_MAX, Math.round(r_raw)));
  return [bestI, r];
}

function alreadyUsedPlayer(point) {
  const k = cellKey(point);
  return state.shipsPlayer.some(s => s.some(c => cellKey(c) === k));
}

playerCanvas.addEventListener('click', (evt) => {
  if (state.phase !== 'place') return;
  if (state.currentShip >= NUM_SHIPS) return;
  const point = clickToPolar(playerCanvas, evt);
  const idx = state.currentShip;
  const ship = state.shipsPlayer[idx];
  const needed = SHIP_SIZES[idx];

  if (alreadyUsedPlayer(point)) {
    setStatus('THAT CELL IS ALREADY USED');
    return;
  }
  if (ship.length > 0) {
    const endpoints = ship.length === 1 ? [ship[0]] : [ship[0], ship[ship.length - 1]];
    if (!endpoints.some(ep => isAdjacent(ep, point))) {
      setStatus('NOT ADJACENT TO EITHER END OF THE SHIP');
      return;
    }
  }
  // Straight-line lock
  const nonOrigin = ship.filter(([_, r]) => r !== 0);
  if (nonOrigin.length >= 2) {
    const radii = new Set(nonOrigin.map(([_, r]) => r));
    const angles = new Set(nonOrigin.map(([a]) => a));
    const [newAi, newR] = point;
    if (radii.size === 1 && newR !== 0 && newR !== [...radii][0]) {
      setStatus(`${SHIP_NAMES[idx]} LOCKED ON RADIUS ${[...radii][0]}`);
      return;
    }
    if (angles.size === 1 && newR !== 0 && newAi !== [...angles][0]) {
      setStatus(`${SHIP_NAMES[idx]} LOCKED ON ANGLE ${piLabel(angleFractions[[...angles][0]])}`);
      return;
    }
  }

  ship.push(point);
  const [ai, r] = point;
  const aLbl = r !== 0 ? piLabel(angleFractions[ai]) : '—';
  setStatus(`${SHIP_NAMES[idx]} ${ship.length}/${needed}: θ=${aLbl}, r=${r}`);

  if (ship.length === needed) {
    state.currentShip++;
    if (state.currentShip === NUM_SHIPS) {
      generateCpuShips();
      startGuessingPhase();
    } else {
      const ni = state.currentShip;
      setStatus(`${SHIP_NAMES[idx]} COMPLETE. NOW PLACING ${SHIP_NAMES[ni]} (${SHIP_SIZES[ni]} PTS)`);
    }
  }
  redrawPlayer();
  renderFleets();
});

// ---------- CPU ships ----------
function generateCpuShips() {
  state.shipsCpu = randomPlaceShips(SHIP_SIZES);
}

// ---------- Guessing phase ----------
function startGuessingPhase() {
  state.phase = 'guess';
  document.body.classList.remove('phase-place');
  document.getElementById('controls').hidden = false;
  buildRadiusButtons();
  buildAngleButtons();
  setStatus('SONAR ACTIVE. SELECT RADIUS AND BEARING, THEN FIRE.');
  // The animation loop's redrawCpu() self-syncs the canvas size every frame,
  // so the layout change is picked up automatically once it reflows.
  redrawPlayer();
}

function buildRadiusButtons() {
  const wrap = document.getElementById('radius-buttons');
  wrap.innerHTML = '';
  for (let r = R_MIN; r <= R_MAX; r++) {
    const b = document.createElement('button');
    b.className = 'radius-btn' + (r === state.selectedRadius ? ' active' : '');
    b.textContent = r;
    b.addEventListener('click', () => {
      state.selectedRadius = r;
      [...wrap.children].forEach((c, i) => c.classList.toggle('active', (R_MIN + i) === r));
    });
    wrap.appendChild(b);
  }
}

function buildAngleButtons() {
  const wrap = document.getElementById('angle-grid');
  wrap.innerHTML = '';
  for (let i = 0; i < N_ANG; i++) {
    const b = document.createElement('button');
    b.className = 'angle-btn' + (i === state.selectedAngleIdx ? ' active' : '');
    b.textContent = piLabel(angleFractions[i]);
    b.addEventListener('click', () => {
      state.selectedAngleIdx = i;
      [...wrap.children].forEach((c, idx) => c.classList.toggle('active', idx === i));
    });
    wrap.appendChild(b);
  }
}

// ---------- Firing ----------
document.getElementById('fire-btn').addEventListener('click', () => fire());

function fire() {
  if (state.phase !== 'guess') return;
  const r = state.selectedRadius;
  const ai = state.selectedAngleIdx;
  const point = [ai, r];
  const k = cellKey(point);
  const aLbl = r !== 0 ? piLabel(angleFractions[ai]) : '—';

  if (state.cpuHits.has(k) || state.cpuMisses.has(k)) {
    setStatus(`(θ=${aLbl}, r=${r}) — ALREADY CALLED`);
    return;
  }

  // Find hit ship
  let hitShipIdx = -1;
  for (let i = 0; i < state.shipsCpu.length; i++) {
    if (state.shipsCpu[i].some(c => cellKey(c) === k)) { hitShipIdx = i; break; }
  }

  if (hitShipIdx >= 0) {
    state.cpuHits.add(k);
    state.cpuHitPoints.push(point);
    const ship = state.shipsCpu[hitShipIdx];
    const sunk = ship.every(c => state.cpuHits.has(cellKey(c)));
    if (sunk) {
      setStatus(`TARGET SUNK: ${SHIP_NAMES[hitShipIdx]}. FIRE AGAIN.`);
      showBanner(`HOSTILE ${SHIP_NAMES[hitShipIdx]} DESTROYED`, 'sunk-hostile');
    } else {
      setStatus(`DIRECT HIT AT (θ=${aLbl}, r=${r}). FIRE AGAIN.`);
    }
    // Victory check
    const allCpuCells = state.shipsCpu.flat().map(cellKey);
    if (allCpuCells.every(ck => state.cpuHits.has(ck))) {
      setStatus('ALL HOSTILES NEUTRALIZED. VICTORY.');
      state.phase = 'done';
      showEndBanner('VICTORY', 'victory');
    }
    redrawCpu();
    renderFleets();
  } else {
    state.cpuMisses.add(k);
    state.cpuMissPoints.push(point);
    setStatus(`MISS AT (θ=${aLbl}, r=${r}). HOSTILE TURN...`);
    redrawCpu();
    setTimeout(computerTurn, 900);
  }
}

// ---------- CPU AI (ported from Python) ----------
function streakOrientation() {
  if (state.cpuHitStreak.length < 2) return [null, null];
  const radii = new Set(state.cpuHitStreak.map(([_, r]) => r));
  if (radii.size === 1 && !radii.has(0)) return ['arc', [...radii][0]];
  const nonOrigin = state.cpuHitStreak.filter(([_, r]) => r !== 0);
  if (nonOrigin.length > 0) {
    const angles = new Set(nonOrigin.map(([a]) => a));
    if (angles.size === 1) return ['radial', [...angles][0]];
  }
  return [null, null];
}

function canonToPoint(canon) {
  const [ai, r] = canon;
  return r === 0 ? [0, 0] : [ai, r];
}

function allPlayerCellsCanonical() {
  const cells = [[-1, 0]];
  for (let ai = 0; ai < N_ANG; ai++) {
    for (let r = 1; r <= R_MAX; r++) cells.push([ai, r]);
  }
  return cells;
}

function pickCpuTarget() {
  const tried = new Set([...state.playerHits, ...state.playerMisses]);

  const [orient, value] = streakOrientation();
  if (orient === 'arc') {
    const r = value;
    const angIndices = state.cpuHitStreak.map(([a]) => a).sort((a, b) => a - b);
    const lo = angIndices[0], hi = angIndices[angIndices.length - 1];
    const candidates = [
      [((lo - 1) % N_ANG + N_ANG) % N_ANG, r],
      [(hi + 1) % N_ANG, r]
    ];
    shuffle(candidates);
    for (const c of candidates) {
      if (!tried.has(cellKey(c))) return c;
    }
  } else if (orient === 'radial') {
    const ai = value;
    const radiiInStreak = state.cpuHitStreak.map(([_, r]) => r).sort((a, b) => a - b);
    const ends = [];
    if (radiiInStreak[0] - 1 >= R_MIN) {
      const rLow = radiiInStreak[0] - 1;
      ends.push(rLow === 0 ? [-1, 0] : [ai, rLow]);
    }
    if (radiiInStreak[radiiInStreak.length - 1] + 1 <= R_MAX) {
      ends.push([ai, radiiInStreak[radiiInStreak.length - 1] + 1]);
    }
    shuffle(ends);
    for (const c of ends) {
      if (!tried.has(cellKey(c))) return canonToPoint(c);
    }
  }

  // Single-hit neighbor probing
  while (state.cpuTargetsQueue.length > 0) {
    const c = state.cpuTargetsQueue.shift();
    if (!tried.has(cellKey(c))) return canonToPoint(c);
  }

  // Hunt mode: random
  const all = allPlayerCellsCanonical().filter(c => !tried.has(cellKey(c)));
  if (all.length === 0) return null;
  return canonToPoint(all[Math.floor(Math.random() * all.length)]);
}

function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
}

function expandNeighbors(target) {
  const tried = new Set([...state.playerHits, ...state.playerMisses]);
  const canon = canonicalCell(target);
  const [orient, value] = streakOrientation();
  let candidates = neighborsCanonical(canon);
  if (orient === 'arc') {
    candidates = candidates.filter(c => c[1] === value);
  } else if (orient === 'radial') {
    candidates = candidates.filter(c => c[0] === value || (c[0] === -1 && c[1] === 0));
  }
  const queueKeys = new Set(state.cpuTargetsQueue.map(cellKey));
  for (const n of candidates) {
    const nk = cellKey(n);
    if (!tried.has(nk) && !queueKeys.has(nk)) {
      state.cpuTargetsQueue.push(n);
      queueKeys.add(nk);
    }
  }
}

function purgeQueueOffLine() {
  const [orient, value] = streakOrientation();
  if (orient === 'arc') {
    state.cpuTargetsQueue = state.cpuTargetsQueue.filter(c => c[1] === value);
  } else if (orient === 'radial') {
    state.cpuTargetsQueue = state.cpuTargetsQueue.filter(
      c => c[0] === value || (c[0] === -1 && c[1] === 0)
    );
  }
}

function shipContaining(point, ships) {
  const k = cellKey(point);
  return ships.find(s => s.some(c => cellKey(c) === k)) || null;
}

function computerTurn() {
  if (state.phase === 'done') return;
  const target = pickCpuTarget();
  if (!target) {
    setStatus('HOSTILE HAS NO TARGETS REMAINING');
    return;
  }
  const [ai, r] = target;
  const aLbl = r !== 0 ? piLabel(angleFractions[ai]) : '—';
  const ship = shipContaining(target, state.shipsPlayer);

  if (ship) {
    state.playerHits.add(cellKey(target));
    state.playerHitPoints.push(target);
    const sunk = ship.every(c => state.playerHits.has(cellKey(c)));
    let sunkShipIdx = -1;
    for (let i = 0; i < state.shipsPlayer.length; i++) {
      if (state.shipsPlayer[i] === ship) { sunkShipIdx = i; break; }
    }

    if (sunk) {
      setStatus(`HOSTILE SUNK YOUR ${SHIP_NAMES[sunkShipIdx]}. FIRING AGAIN...`);
      showBanner(`FRIENDLY ${SHIP_NAMES[sunkShipIdx]} LOST`, 'sunk-friendly');
      // Clear streak/queue for this ship
      const shipKeys = new Set(ship.map(cellKey));
      state.cpuHitStreak = state.cpuHitStreak.filter(c => !shipKeys.has(cellKey(c)));
      state.cpuTargetsQueue = state.cpuTargetsQueue.filter(c => !shipKeys.has(cellKey(c)));
    } else {
      state.cpuHitStreak.push(target);
      expandNeighbors(target);
      purgeQueueOffLine();
      setStatus(`HOSTILE HIT AT (θ=${aLbl}, r=${r}). FIRING AGAIN...`);
    }

    // Defeat check
    const allPlayerCells = state.shipsPlayer.flat().map(cellKey);
    if (allPlayerCells.every(ck => state.playerHits.has(ck))) {
      setStatus('ALL FRIENDLIES DESTROYED. DEFEAT.');
      state.phase = 'done';
      showEndBanner('DEFEAT', 'defeat');
      redrawPlayer();
      renderFleets();
      return;
    }

    redrawPlayer();
    renderFleets();

    if (state.phase !== 'done') {
      setTimeout(computerTurn, 1000);
    }
  } else {
    state.playerMisses.add(cellKey(target));
    state.playerMissPoints.push(target);
    setStatus(`HOSTILE MISS AT (θ=${aLbl}, r=${r}). YOUR TURN — FIRE.`);
    redrawPlayer();
  }
}

// ---------- Clock ----------
function tickClock() {
  const d = new Date();
  const hh = String(d.getHours()).padStart(2, '0');
  const mm = String(d.getMinutes()).padStart(2, '0');
  const ss = String(d.getSeconds()).padStart(2, '0');
  document.getElementById('clock').textContent = `${hh}:${mm}:${ss}`;
}
setInterval(tickClock, 1000);
tickClock();

// ---------- Reset ----------
function resetGame() {
  // Wipe state in place so existing references stay valid
  state.phase = 'place';
  state.shipsPlayer = [[], [], []];
  state.currentShip = 0;
  state.shipsCpu = [];
  state.cpuHits.clear();
  state.cpuMisses.clear();
  state.cpuHitPoints.length = 0;
  state.cpuMissPoints.length = 0;
  state.playerHits.clear();
  state.playerMisses.clear();
  state.playerHitPoints.length = 0;
  state.playerMissPoints.length = 0;
  state.cpuTargetsQueue.length = 0;
  state.cpuHitStreak.length = 0;
  state.selectedRadius = 1;
  state.selectedAngleIdx = 0;
  state.pings.length = 0;

  // Hide banner + controls
  document.getElementById('banner').className = 'banner hidden';
  document.getElementById('controls').hidden = true;
  document.body.classList.add('phase-place');

  setStatus(`DEPLOY YOUR FLEET — PLACE THE ${SHIP_NAMES[0]} (${SHIP_SIZES[0]} POINTS). CLICK THE FRIENDLY GRID TO BEGIN.`);
  renderFleets();
  // redrawCpu()/redrawPlayer() self-sync the canvas size each call, so the
  // layout change is handled automatically.
  redrawPlayer();
}

// ---------- Init ----------
setStatus(`DEPLOY YOUR FLEET — PLACE THE ${SHIP_NAMES[0]} (${SHIP_SIZES[0]} POINTS). CLICK THE FRIENDLY GRID TO BEGIN.`);
renderFleets();
redrawAll();
