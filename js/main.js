// ═══════════════════════════════════════════════════════════════════
//  CHARSETS  dark→light
// ═══════════════════════════════════════════════════════════════════
const CS = {
  ultra:   '$@B%8&WM#oahkbdpqwmZO0QLCJUYXzcvunxrjft/|()1{}[]?-_+~<>i!lI;:,"^`\'. ',
  detail:  '@#S%?*+;:,. ',
  std:     '@#+:. ',
  minimal: '@ . ',
  blocks:  '█▓▒░ ',
  braille: '⣿⣷⣯⣟⣻⡿⢿⣾⣤⠄⠀',
  matrix:  '日ﾊﾐﾋｰｳｼﾅﾓﾆｻﾜﾂｵﾘｱﾎﾃﾏｹﾒｴｶｷﾑﾕﾗｾﾈｽﾀﾇﾍ012345789Z ',
  hex:     '0123456789ABCDEF ',
};
const PALETTE = {
  white:'#e0e0e0',green:'#00ff87',acid:'#e8ff47',amber:'#ff9f43',
  cyan:'#00d2ff',pink:'#ff6b9d',violet:'#a29bfe',rose:'#fd79a8',
};

// ═══════════════════════════════════════════════════════════════════
//  STATE
// ═══════════════════════════════════════════════════════════════════
let cols=220, zoom=1.0;
let csKey='detail', charset=CS.detail;
let mirror=true, invert=false, colorMode=false, lightBg=false, bold=false;
let brightness=0, contrast=1.0, gamma=1.0, sharpen=0;
let fx={edge:false,scanline:false,glitch:false,pixelate:false,thermal:false,ghost:false,rain:false};
let currentColor='#e0e0e0';
let frozen=false, freezePixels=null;
let stream=null, video=null, animId=null;
let lastTime=0, fpsSmooth=0, frameCount=0;

// ═══════════════════════════════════════════════════════════════════
//  CANVASES
// ═══════════════════════════════════════════════════════════════════
const vp      = document.getElementById('vp');
const display = document.getElementById('display');
const dCtx    = display.getContext('2d');

const rainEffect = document.getElementById('rain-effect');
const rCtx = rainEffect.getContext('2d');
let rainDrops = [];

const sample  = document.createElement('canvas');
const sCtx    = sample.getContext('2d', {willReadFrequently:true});

// Persistent pixelate scratch canvas (avoids per-frame allocation)
const pixScratch = document.createElement('canvas');
const pxCtx  = pixScratch.getContext('2d');
pxCtx.imageSmoothingEnabled = false;

// Ghost accumulation canvas
const ghostCv = document.createElement('canvas');
const gCtx    = ghostCv.getContext('2d', {willReadFrequently:true});

// Pre-allocated Sobel output buffer (resized only when grid changes)
let sobelBuf = null;
let sobelW=0, sobelH=0;

// Pre-allocated line char buffer (avoid string concat at high cols)
let lineBuf = null; // Uint16Array for charCodes

// ═══════════════════════════════════════════════════════════════════
//  LUT
// ═══════════════════════════════════════════════════════════════════
let lut           = new Uint8Array(256);  // brightness/contrast/gamma adjusted value
let charIdxLut    = new Uint8Array(256);  // luma → charset index (post-lut)
let directCharLut = new Uint8Array(256);  // raw pixel → charset index (combined, avoids double lookup)
let lutDirty      = true;

// Pre-baked rgb() string table — 32 levels per channel (5-bit quantised), 32768 entries
// Stored as flat array indexed by (r5<<10)|(g5<<5)|b5
// Built lazily on first color-mode frame to avoid startup cost
let rgbStrCache = null;
function buildRgbCache() {
  rgbStrCache = new Array(32768);
  for (let r=0;r<32;r++) for (let g=0;g<32;g++) for (let b=0;b<32;b++) {
    rgbStrCache[(r<<10)|(g<<5)|b] = `rgb(${r<<3},${g<<3},${b<<3})`;
  }
}

function rebuildLuts() {
  const cl = charset.length - 1;
  for (let i=0; i<256; i++) {
    let v = i * contrast + brightness;
    v = v<0?0:v>255?255:v|0;
    v = Math.round(Math.pow(v/255, 1/gamma) * 255);
    lut[i] = v;
    charIdxLut[i] = Math.floor(i / 255 * cl);
  }
  // Build combined raw→charIdx LUT so render loop does 1 lookup instead of 2
  for (let i=0;i<256;i++) {
    directCharLut[i] = charIdxLut[lut[i]];
  }
  lutDirty = false;
}
rebuildLuts();

// Thermal palette pre-baked as flat RGB array (256×3) — no per-pixel allocation
const thermalR = new Uint8Array(256);
const thermalG = new Uint8Array(256);
const thermalB = new Uint8Array(256);
(function buildThermal(){
  for (let i=0;i<256;i++){
    if      (i<64)  { thermalR[i]=i*2;             thermalG[i]=0;           thermalB[i]=i*4; }
    else if (i<128) { thermalR[i]=128+(i-64)*2;    thermalG[i]=0;           thermalB[i]=255-(i-64)*4; }
    else if (i<192) { thermalR[i]=255;              thermalG[i]=(i-128)*4;  thermalB[i]=0; }
    else            { thermalR[i]=255;              thermalG[i]=255;         thermalB[i]=(i-192)*4; }
  }
})();

// Pre-baked scanline pattern — one offscreen canvas, redrawn only on resize
let scanPat = null, scanPatVw = 0, scanPatVh = 0;
function getScanPattern(vw, vh) {
  if (scanPat && scanPatVw===vw && scanPatVh===vh) return scanPat;
  const sc = document.createElement('canvas');
  sc.width=vw; sc.height=vh;
  const sx = sc.getContext('2d');
  sx.fillStyle = 'rgba(0,0,0,0.38)';
  for (let y=0;y<vh;y+=2) sx.fillRect(0,y,vw,1);
  scanPat = sc; scanPatVw=vw; scanPatVh=vh;
  return scanPat;
}
let scanPatLight = null, scanPatLightVw = 0, scanPatLightVh = 0;
function getScanPatternLight(vw, vh) {
  if (scanPatLight && scanPatLightVw===vw && scanPatLightVh===vh) return scanPatLight;
  const sc = document.createElement('canvas');
  sc.width=vw; sc.height=vh;
  const sx = sc.getContext('2d');
  sx.fillStyle = 'rgba(0,0,0,0.07)';
  for (let y=0;y<vh;y+=2) sx.fillRect(0,y,vw,1);
  scanPatLight = sc; scanPatLightVw=vw; scanPatLightVh=vh;
  return scanPatLight;
}
let charW=0, charH=0, lastGridKey='';
// Persistent glitch array — reallocated only when nRows grows
let glitchRow = new Int16Array(512);
// Persistent string-build array for fast row rendering
let rowChars = new Array(512);
// Persistent Uint16Array for fromCharCode fast path
let rowCodes = new Uint16Array(1024);
// Pre-built charCode LUT for current charset — rebuilt only when charset changes
let ccLut = new Uint16Array(256);
function buildCcLut() {
  for (let i=0;i<charset.length;i++) ccLut[i] = charset.charCodeAt(i);
}
buildCcLut();

function recomputeGrid() {
  const vw=vp.clientWidth, vh=vp.clientHeight;
  const dpr=window.devicePixelRatio||1;
  const key=`${cols}|${vw}|${vh}|${bold}|${zoom}|${dpr}`;
  if (key===lastGridKey) return;
  lastGridKey=key;

  const effectiveCols = Math.max(1, Math.round(cols/zoom));
  let fs = vw / effectiveCols / 0.601;
  fs = Math.max(2.5, Math.min(48, fs));

  const weight = bold?'600':'400';
  const fontStr = `${weight} ${fs}px "DM Mono",monospace`;

  // Physical pixel dimensions — critical fix for overflow at non-100% display scaling
  display.width  = Math.round(vw  * dpr);
  display.height = Math.round(vh  * dpr);
  display.style.width  = vw  + 'px';
  display.style.height = vh  + 'px';

  // Scale context so we work in CSS pixels throughout
  dCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
  dCtx.font = fontStr;
  dCtx.textBaseline = 'top';

  charW = dCtx.measureText('M').width;
  charH = fs;

  // Grow persistent buffers if needed
  const maxCols = Math.ceil(vw / charW) + 4;
  if (maxCols > rowChars.length) rowChars = new Array(maxCols);
  lineBuf = new Uint8Array(maxCols); // byte-sized is enough for ASCII/latin
}

// ═══════════════════════════════════════════════════════════════════
//  CAMERA
// ═══════════════════════════════════════════════════════════════════
async function startCam() {
  document.getElementById('overlay').style.display='none';
  try {
    stream = await navigator.mediaDevices.getUserMedia({
      video:{facingMode:'user',width:{ideal:1920},height:{ideal:1080}},audio:false
    });
    video = document.createElement('video');
    video.srcObject=stream;
    video.autoplay=video.playsInline=video.muted=true;
    video.play();
    video.addEventListener('playing', ()=>{
      document.getElementById('rec').classList.add('live');
      requestAnimationFrame(renderLoop);
    });
  } catch(e) {
    document.getElementById('overlay').style.display='flex';
    const btn=document.getElementById('go');
    btn.textContent='Retry — Allow Camera';
    btn.style.background='#ff4757';
    btn.onclick=()=>location.reload();
  }
}

// ═══════════════════════════════════════════════════════════════════
//  SOBEL — operates in-place on a pre-allocated output buffer
// ═══════════════════════════════════════════════════════════════════
function sobelPass(pixels, w, h) {
  // Resize buffer only when grid changes
  if (sobelW!==w || sobelH!==h) {
    sobelBuf = new Uint8ClampedArray(w*h*4);
    sobelW=w; sobelH=h;
  }
  sobelBuf.fill(0);
  for (let y=1;y<h-1;y++) {
    for (let x=1;x<w-1;x++) {
      const tl=(77*pixels[((y-1)*w+x-1)*4]+151*pixels[((y-1)*w+x-1)*4+1]+28*pixels[((y-1)*w+x-1)*4+2])>>8;
      const tm=(77*pixels[((y-1)*w+x  )*4]+151*pixels[((y-1)*w+x  )*4+1]+28*pixels[((y-1)*w+x  )*4+2])>>8;
      const tr=(77*pixels[((y-1)*w+x+1)*4]+151*pixels[((y-1)*w+x+1)*4+1]+28*pixels[((y-1)*w+x+1)*4+2])>>8;
      const ml=(77*pixels[( y   *w+x-1)*4]+151*pixels[( y   *w+x-1)*4+1]+28*pixels[( y   *w+x-1)*4+2])>>8;
      const mr=(77*pixels[( y   *w+x+1)*4]+151*pixels[( y   *w+x+1)*4+1]+28*pixels[( y   *w+x+1)*4+2])>>8;
      const bl=(77*pixels[((y+1)*w+x-1)*4]+151*pixels[((y+1)*w+x-1)*4+1]+28*pixels[((y+1)*w+x-1)*4+2])>>8;
      const bm=(77*pixels[((y+1)*w+x  )*4]+151*pixels[((y+1)*w+x  )*4+1]+28*pixels[((y+1)*w+x  )*4+2])>>8;
      const br=(77*pixels[((y+1)*w+x+1)*4]+151*pixels[((y+1)*w+x+1)*4+1]+28*pixels[((y+1)*w+x+1)*4+2])>>8;
      const gx=-tl-2*ml-bl+tr+2*mr+br;
      const gy=-tl-2*tm-tr+bl+2*bm+br;
      const mag=Math.min(255, (gx*gx+gy*gy) * 0.007 | 0); // avoid sqrt: use squared * scale
      const idx=(y*w+x)*4;
      sobelBuf[idx]=sobelBuf[idx+1]=sobelBuf[idx+2]=mag;
      sobelBuf[idx+3]=255;
    }
  }
  return sobelBuf;
}

// ═══════════════════════════════════════════════════════════════════
//  RENDER LOOP
// ═══════════════════════════════════════════════════════════════════
function drawRain() {
    if (!fx.rain) {
        rainEffect.style.display = 'none';
        return;
    }
    rainEffect.style.display = 'block';

    const vw = vp.clientWidth;
    const vh = vp.clientHeight;
    const dpr = window.devicePixelRatio || 1;

    rainEffect.width = Math.round(vw * dpr);
    rainEffect.height = Math.round(vh * dpr);
    rCtx.setTransform(dpr, 0, 0, dpr, 0, 0);

    const fontSize = 16;
    const columns = Math.floor(vw / fontSize);

    if (rainDrops.length === 0) {
        for (let i = 0; i < columns; i++) {
            rainDrops[i] = 1;
        }
    }

    rCtx.fillStyle = 'rgba(0, 0, 0, 0.05)';
    rCtx.fillRect(0, 0, vw, vh);

    rCtx.fillStyle = '#0F0';
    rCtx.font = fontSize + 'px monospace';

    for (let i = 0; i < rainDrops.length; i++) {
        const text = CS.matrix.charAt(Math.floor(Math.random() * CS.matrix.length));
        rCtx.fillText(text, i * fontSize, rainDrops[i] * fontSize);

        if (rainDrops[i] * fontSize > vh && Math.random() > 0.975) {
            rainDrops[i] = 0;
        }
        rainDrops[i]++;
    }
}
function renderLoop(ts) {
  animId = requestAnimationFrame(renderLoop);
  if (!video || video.readyState<2) return;

  drawRain();

  const delta = ts - lastTime;
  if (delta < 16) return;
  lastTime = ts;
  fpsSmooth = fpsSmooth*0.9 + (1000/delta)*0.1;
  frameCount++;

  recomputeGrid();

  const vw=vp.clientWidth, vh=vp.clientHeight;
  // Clamp to actual canvas pixels to prevent overflow
  const nCols = Math.min(Math.floor(vw/charW), display.width  / charW | 0);
  const nRows = Math.min(Math.floor(vh/charH), display.height / charH | 0);

  // ── SAMPLE ─────────────────────────────────────────────────────────
  let pixels;
  if (frozen && freezePixels) {
    pixels = freezePixels;
  } else {
    if (sample.width!==nCols || sample.height!==nRows) {
      sample.width=nCols; sample.height=nRows;
    }

    sCtx.save();
    if (mirror) { sCtx.translate(nCols,0); sCtx.scale(-1,1); }

    const vAsp=video.videoWidth/video.videoHeight;
    const cAsp=nCols/nRows;
    let sx=0,sy=0,sw=video.videoWidth,sh=video.videoHeight;
    if (vAsp>cAsp) { sw=sh*cAsp; sx=(video.videoWidth-sw)/2; }
    else           { sh=sw/cAsp; sy=(video.videoHeight-sh)/2; }
    if (zoom!==1.0) {
      const zf=1/zoom, zw=sw*zf, zh=sh*zf;
      sx+=(sw-zw)/2; sy+=(sh-zh)/2; sw=zw; sh=zh;
    }

    if (sharpen>0) {
      sCtx.drawImage(video,sx,sy,sw,sh,0,0,nCols,nRows);
      sCtx.globalCompositeOperation='luminosity';
      sCtx.globalAlpha=sharpen*0.006;
      sCtx.filter='blur(1px)';
      sCtx.drawImage(video,sx,sy,sw,sh,0,0,nCols,nRows);
      sCtx.filter='none'; sCtx.globalAlpha=1; sCtx.globalCompositeOperation='source-over';
    } else {
      sCtx.drawImage(video,sx,sy,sw,sh,0,0,nCols,nRows);
    }
    sCtx.restore();

    // Pixelate — use persistent scratch canvas, no new canvas each frame
    if (fx.pixelate) {
      const pw=Math.max(1,nCols>>2), ph=Math.max(1,nRows>>2);
      if (pixScratch.width!==pw || pixScratch.height!==ph) {
        pixScratch.width=pw; pixScratch.height=ph;
      }
      pxCtx.drawImage(sample,0,0,pw,ph);
      sCtx.imageSmoothingEnabled=false;
      sCtx.drawImage(pixScratch,0,0,pw,ph,0,0,nCols,nRows);
      sCtx.imageSmoothingEnabled=true;
    }

    pixels = sCtx.getImageData(0,0,nCols,nRows).data;

    // Ghost trail — blend with ghost accumulation buffer
    if (fx.ghost) {
      if (ghostCv.width!==nCols || ghostCv.height!==nRows) {
        ghostCv.width=nCols; ghostCv.height=nRows;
      }
      const gd = gCtx.getImageData(0,0,nCols,nRows).data;
      // pixels is a read-only Uint8ClampedArray from getImageData — copy it
      const blended = new Uint8ClampedArray(pixels.length);
      for (let i=0;i<pixels.length;i+=4) {
        blended[i]  =(pixels[i]  *3+gd[i]  )>>2;
        blended[i+1]=(pixels[i+1]*3+gd[i+1])>>2;
        blended[i+2]=(pixels[i+2]*3+gd[i+2])>>2;
        blended[i+3]=255;
      }
      pixels = blended;
      // Update ghost buffer with current sample
      gCtx.drawImage(sample,0,0);
    }

    if (fx.edge) pixels = sobelPass(pixels, nCols, nRows);
  }

  if (lutDirty) rebuildLuts();

  // Fill the FULL viewport with background first (before clip)
  // so any gap between grid edge and canvas edge is black, not transparent
  dCtx.fillStyle = lightBg?'#ffffff':'#000000';
  dCtx.fillRect(0, 0, vp.clientWidth, vp.clientHeight);

  // Clip strictly to the character grid — only needed when glitch is active
  // (glitch can shift rows outside bounds; normally nothing bleeds)
  dCtx.save();
  if (fx.glitch) {
    dCtx.beginPath();
    dCtx.rect(0, 0, nCols*charW, nRows*charH);
    dCtx.clip();
  }

  // Glitch offsets — reuse a fixed-size Int16Array, only fill the used range
  const doGlitch = fx.glitch && Math.random()<0.3;
  // Use persistent glitch buffer — grow only if needed
  if (glitchRow.length < nRows) glitchRow = new Int16Array(nRows + 64);
  else glitchRow.fill(0, 0, nRows);
  if (doGlitch) {
    const bands=(Math.random()*3+1)|0;
    for (let b=0;b<bands;b++) {
      const start=(Math.random()*nRows)|0;
      const len=(Math.random()*6+2)|0;
      const shift=((Math.random()-0.5)*10)|0;
      for (let r=start;r<Math.min(nRows,start+len);r++) glitchRow[r]=shift;
    }
  }

  const useFastPath = !colorMode && !fx.thermal;

  if (useFastPath) {
    // ── FAST PATH: one fillText per row using fromCharCode on Uint16Array ──
    // Grow rowCodes buffer if needed
    if (rowCodes.length < nCols) rowCodes = new Uint16Array(nCols + 64);

    // Combine lut+charIdxLut into one directCharLut pass (already built)
    // For lightBg invert the luma index: charset[cl - directCharLut[lm]]
    const cl = charset.length - 1;
    dCtx.fillStyle = lightBg?'#111':currentColor;
    for (let row=0;row<nRows;row++) {
      const rb=row*nCols*4;
      if (lightBg) {
        for (let col=0;col<nCols;col++) {
          const pi=rb+col*4;
          let lm=(77*pixels[pi]+151*pixels[pi+1]+28*pixels[pi+2])>>8;
          if (invert) lm=255-lm;
          rowCodes[col] = ccLut[cl - directCharLut[lm]];
        }
      } else if (invert) {
        for (let col=0;col<nCols;col++) {
          const pi=rb+col*4;
          const lm=255-((77*pixels[pi]+151*pixels[pi+1]+28*pixels[pi+2])>>8);
          rowCodes[col] = ccLut[directCharLut[lm]];
        }
      } else {
        for (let col=0;col<nCols;col++) {
          const pi=rb+col*4;
          rowCodes[col] = ccLut[directCharLut[(77*pixels[pi]+151*pixels[pi+1]+28*pixels[pi+2])>>8]];
        }
      }
      dCtx.fillText(String.fromCharCode(...rowCodes.subarray(0,nCols)), glitchRow[row]*charW, row*charH);
    }
  } else {
    // ── COLOR/THERMAL PATH: batch consecutive same-color spans ───────────
    if (!rgbStrCache) buildRgbCache();
    const cl = charset.length - 1;
    for (let row=0;row<nRows;row++) {
      const y=row*charH;
      const rb=row*nCols*4;
      const xOff=glitchRow[row]*charW;
      let bStr='', bX=0, lastKey=-1;

      for (let col=0;col<=nCols;col++) {
        if (col<nCols) {
          const pi=rb+col*4;
          let r=lut[pixels[pi]], g=lut[pixels[pi+1]], b=lut[pixels[pi+2]];
          let lm=(77*r+151*g+28*b)>>8;
          if (invert){lm=255-lm;r=255-r;g=255-g;b=255-b;}

          let fr=r,fg=g,fb=b;
          if (fx.thermal){fr=thermalR[lm];fg=thermalG[lm];fb=thermalB[lm];}

          const ch=charset[charIdxLut[lightBg?255-lm:lm]];
          const qkey=((fr>>3)<<10)|((fg>>3)<<5)|(fb>>3);

          if (qkey===lastKey) {
            bStr+=ch;
          } else {
            if (bStr) dCtx.fillText(bStr, xOff+bX*charW, y);
            dCtx.fillStyle = rgbStrCache[qkey];
            bStr=ch; bX=col; lastKey=qkey;
          }
        } else {
          if (bStr) dCtx.fillText(bStr, xOff+bX*charW, y);
        }
      }
    }
  }

  // Only clip when glitch is active (saves expensive clip setup every frame)
  dCtx.restore();

  // ── SCANLINES — single drawImage instead of N fillRect calls ──────────
  if (fx.scanline) {
    const pat = lightBg ? getScanPatternLight(vw,vh) : getScanPattern(vw,vh);
    dCtx.drawImage(pat, 0, 0);
  }

  // ── STATS ──────────────────────────────────────────────────────────
  if (frameCount%6===0) {
    const fps=Math.round(fpsSmooth);
    document.getElementById('h-fps').textContent =`${fps} FPS`;
    document.getElementById('h-res').textContent =`${nCols}×${nRows}`;
    document.getElementById('i-fps').textContent =fps;
    document.getElementById('i-cols').textContent=nCols;
    document.getElementById('i-rows').textContent=nRows;
    document.getElementById('i-chars').textContent=((nCols*nRows)/1000).toFixed(1)+'k';
  }
}

// ═══════════════════════════════════════════════════════════════════
//  CONTROLS
// ═══════════════════════════════════════════════════════════════════
function setCs(el) {
  document.querySelectorAll('[data-cs]').forEach(c=>c.classList.remove('on'));
  el.classList.add('on');
  csKey=el.dataset.cs; charset=CS[csKey];
  document.getElementById('h-mode').textContent=csKey.toUpperCase();
  lastGridKey=''; lutDirty=true;
  sobelW=0; sobelH=0; // force sobel buf resize
  rebuildLuts(); // charset length changed, must rebuild directCharLut immediately
  buildCcLut();  // rebuild charCode LUT for new charset
}
function setCols(v){cols=parseInt(v);document.getElementById('v-cols').textContent=v;lastGridKey='';}
function setZoom(v){zoom=v/100;document.getElementById('v-zoom').textContent=zoom.toFixed(1)+'×';}
function setColor(name,el){
    document.querySelectorAll('.sw').forEach(s=>s.classList.remove('on'));
    el.classList.add('on');
    currentColor=PALETTE[name];
}
function setBr(v){brightness=parseInt(v);document.getElementById('v-br').textContent=(v>0?'+':'')+v;lutDirty=true;}
function setCt(v){contrast=v/100;document.getElementById('v-ct').textContent=contrast.toFixed(1)+'×';lutDirty=true;}
function setGamma(v){gamma=v/100;document.getElementById('v-gm').textContent=gamma.toFixed(1);lutDirty=true;}
function setSharpen(v){sharpen=parseInt(v);document.getElementById('v-sh').textContent=v;}
function toggleFx(el){const k=el.dataset.fx;fx[k]=!fx[k];el.classList.toggle('on',fx[k]);}
function toggleOpt(key,btn){
  if(key==='mirror')   mirror   =!mirror;
  if(key==='invert')   invert   =!invert;
  if(key==='colorMode')colorMode=!colorMode;
  if(key==='lightBg')  lightBg  =!lightBg;
  if(key==='bold')     {bold=!bold;lastGridKey='';}
  btn.classList.toggle('on');
}
function toggleFreeze(){
  frozen=!frozen;
  if(frozen){
    const nC=Math.floor(vp.clientWidth/charW), nR=Math.floor(vp.clientHeight/charH);
    freezePixels=new Uint8ClampedArray(sCtx.getImageData(0,0,nC,nR).data);
    document.getElementById('freeze-badge').classList.add('on');
    document.getElementById('freeze-btn').classList.add('on');
    document.getElementById('freeze-btn').textContent='▶ Unfreeze';
  } else {
    freezePixels=null;
    document.getElementById('freeze-badge').classList.remove('on');
    document.getElementById('freeze-btn').classList.remove('on');
    document.getElementById('freeze-btn').textContent='⏸ Freeze Frame';
  }
}

// ═══════════════════════════════════════════════════════════════════
//  EXPORT
// ═══════════════════════════════════════════════════════════════════
function snap(mode){
  if(mode==='dark'){
    const a=document.createElement('a');
    a.download=`ascii-cam-${Date.now()}.png`;
    a.href=display.toDataURL('image/png'); a.click(); return;
  }
  const vw=vp.clientWidth, vh=vp.clientHeight;
  const nC=Math.floor(vw/charW), nR=Math.floor(vh/charH);
  const sc=document.createElement('canvas');
  const sf=charH*2;
  sc.width=vw*2; sc.height=vh*2;
  const sc2=sc.getContext('2d');
  const wt=bold?'600':'400';
  sc2.font=`${wt} ${sf}px "DM Mono",monospace`;
  sc2.textBaseline='top';
  sc2.fillStyle='#fff'; sc2.fillRect(0,0,sc.width,sc.height);
  const pix=freezePixels||sCtx.getImageData(0,0,nC,nR).data;
  const cl=charset.length-1;
  sc2.fillStyle='#111';
  for(let row=0;row<nR;row++){
    let line='';
    const rb=row*nC*4;
    for(let col=0;col<nC;col++){
      const pi=rb+col*4;
      const r=lut[pix[pi]],g=lut[pix[pi+1]],b=lut[pix[pi+2]];
      let lm=(77*r+151*g+28*b)>>8;
      if(invert)lm=255-lm;
      line+=charset[Math.floor((255-lm)/255*cl)];
    }
    sc2.fillText(line,0,row*sf);
  }
  const a=document.createElement('a');
  a.download=`ascii-cam-share-${Date.now()}.png`; a.href=sc.toDataURL('image/png'); a.click();
}

// Force full grid recompute + immediate redraw on resize / orientation change
new ResizeObserver(() => { lastGridKey = ''; }).observe(vp);

function copyText(){
  const nC=Math.floor(vp.clientWidth/charW), nR=Math.floor(vp.clientHeight/charH);
  const pix=freezePixels||sCtx.getImageData(0,0,nC,nR).data;
  const cl=charset.length-1;
  let out='';
  for(let row=0;row<nR;row++){
    for(let col=0;col<nC;col++){
      const pi=(row*nC+col)*4;
      const lm=(77*pix[pi]+151*pix[pi+1]+28*pix[pi+2])>>8;
      out+=charset[charIdxLut[invert?255-lm:lm]];
    }
    out+='\n';
  }
  navigator.clipboard.writeText(out).then(()=>{
    const btn=document.querySelector('.abtn:last-child');
    const orig=btn.textContent;
    btn.textContent='✓ Copied!';
    setTimeout(()=>btn.textContent=orig,1800);
  });
}

document.getElementById('go').addEventListener('click', startCam);

document.getElementById('charset-chips').addEventListener('click', (e) => {
    if (e.target.classList.contains('chip')) {
        setCs(e.target);
    }
});

document.getElementById('cols-slider').addEventListener('input', (e) => {
    setCols(e.target.value);
});

document.getElementById('zoom-slider').addEventListener('input', (e) => {
    setZoom(e.target.value);
});

document.getElementById('color-swatches').addEventListener('click', (e) => {
    if (e.target.classList.contains('sw')) {
        setColor(e.target.dataset.color, e.target);
    }
});

document.getElementById('br-slider').addEventListener('input', (e) => {
    setBr(e.target.value);
});

document.getElementById('ct-slider').addEventListener('input', (e) => {
    setCt(e.target.value);
});

document.getElementById('gamma-slider').addEventListener('input', (e) => {
    setGamma(e.target.value);
});

document.getElementById('sharpen-slider').addEventListener('input', (e) => {
    setSharpen(e.target.value);
});

document.getElementById('fx-chips').addEventListener('click', (e) => {
    if (e.target.classList.contains('chip')) {
        toggleFx(e.target);
    }
});

document.getElementById('options-sec').addEventListener('click', (e) => {
    if (e.target.classList.contains('tog')) {
        toggleOpt(e.target.dataset.opt, e.target);
    }
});

document.getElementById('freeze-btn').addEventListener('click', toggleFreeze);
document.getElementById('snap-dark').addEventListener('click', () => snap('dark'));
document.getElementById('snap-share').addEventListener('click', () => snap('share'));
document.getElementById('copy-text').addEventListener('click', copyText);
