/* Offline replay. B/C are exploratory references, never treated as ground truth. */
(() => {
  'use strict';
  const $=id=>document.getElementById(id), cases=[...window.REPORT_DATA].sort((a,b)=>(a.paired_gap.mean_m??Infinity)-(b.paired_gap.mean_m??Infinity));
  const byId=Object.fromEntries(cases.map(c=>[c.id,c]));
  const videos=Object.fromEntries('ABC'.split('').map(c=>[c,$('v'+c)]));
  const overlays=Object.fromEntries('ABC'.split('').map(c=>[c,$('o'+c)]));
  const courts=Object.fromEntries('ABC'.split('').map(c=>[c,$('court'+c)]));
  const courtKeys={A:null,B:null,C:null},dirty={A:[],B:[],C:[]};
  const displayed=Object.fromEntries('ABC'.split('').map(c=>[c,null]));
  const frameCallback=Object.fromEntries('ABC'.split('').map(c=>[c,typeof videos[c].requestVideoFrameCallback==='function']));
  const lastCorrection={B:0,C:0};
  let data, yaw=-.62, pitch=.80, drag=null, loadVersion=0, expanded=null, suppressPlotClick=false, playbackEpoch=0, resyncing=false;
  let lastControlsUpdate=0,loading=false;
  const visibleStart=c=>0;
  const visibleDuration=c=>Math.max(0,c.duration_s-visibleStart(c));
  const outline=[[-3.05,-6.7,0],[3.05,-6.7,0],[3.05,6.7,0],[-3.05,6.7,0],[-3.05,-6.7,0]];
  const lines=[];for(let i=0;i<4;i++)lines.push([outline[i],outline[i+1]]);
  for(const x of [-2.59,2.59])lines.push([[x,-6.7,0],[x,6.7,0]]);
  for(const y of [-5.94,-1.98,1.98,5.94])lines.push([[-3.05,y,0],[3.05,y,0]]);
  lines.push([[0,-6.7,0],[0,-1.98,0]],[[0,1.98,0],[0,6.7,0]]);
  const groundCount=lines.length;
  lines.push([[-3.05,0,0],[-3.05,0,1.55]],[[3.05,0,0],[3.05,0,1.55]],[[-3.05,0,1.55],[3.05,0,1.55]]);
  function nearest(a,t,key='t'){
    if(!a||!a.length)return null;let lo=0,hi=a.length;
    while(lo<hi){const mid=(lo+hi)>>1;if(a[mid][key]<t)lo=mid+1;else hi=mid}
    const p=[a[lo-1],a[lo]].filter(Boolean);return p.reduce((a,b)=>Math.abs(a[key]-t)<=Math.abs(b[key]-t)?a:b);
  }
  function project(cam,p){
    if(!cam||!p)return null;const q=p.map((x,i)=>x-cam.C[i]);const v=cam.R.map(r=>r.reduce((s,x,i)=>s+x*q[i],0));
    if(v[2]<=0)return null;let x=v[0]/v[2],y=v[1]/v[2];
    const d=cam.dist||[cam.k1||0,0,0,0,0],r=x*x+y*y,radial=1+(d[0]||0)*r+(d[1]||0)*r*r+(d[4]||0)*r*r*r;
    const xx=x*radial+2*(d[2]||0)*x*y+(d[3]||0)*(r+2*x*x),yy=y*radial+(d[2]||0)*(r+2*y*y)+2*(d[3]||0)*x*y;
    return [cam.K[0][0]*xx+(cam.K[0][1]||0)*yy+cam.K[0][2],cam.K[1][1]*yy+cam.K[1][2]];
  }
  function mapped(k,p){if(!p)return null;if(k==='C'&&$('cropC').checked&&data.C_crop_xywh)return[p[0]-data.C_crop_xywh[0],p[1]-data.C_crop_xywh[1]];return p}
  function motionInfo(){return window.DYNAMIC_CAMERAS[data.id]}
  function frameIndex(t,info){return Math.max(0,Math.min(info.H.length-1,Math.round(t*info.fps)))}
  function calIndex(t,info){return Math.max(0,Math.min(info.R.length-1,Math.round(t*info.fps)))}
  function framePoint(k,p,t){
    if(k==='A'&&$('cameraMode').value==='redetect'){const a=window.FRAME_CAL[data.id];if(!a)return null;const i=calIndex(t,a);if(!a.valid[i])return null;return project({K:a.K,R:a.R[i],C:a.C[i],k1:0},p)}
    let q=project(data.cameras[k],p);if(k!=='A'||$('cameraMode').value==='fixed'||!q)return q;
    const info=motionInfo();if(!info)return null;const i=frameIndex(t,info),h=info.H[i];if(!h||!info.valid[i])return null;
    const d=h[6]*q[0]+h[7]*q[1]+h[8];if(Math.abs(d)<1e-9)return null;
    return [(h[0]*q[0]+h[1]*q[1]+h[2])/d,(h[3]*q[0]+h[4]*q[1]+h[5])/d];
  }
  function paired(){const info=motionInfo();if(!info)return null;const p=info.full;
    return p&&p.fixed_physics_converged&&p.rotational_physics_converged?p:info.network||null;
  }
  function mono(f){if($('cameraMode').value==='redetect'){const a=window.FRAME_CAL[data.id],i=calIndex(f.t,a);return (a.full&&a.full.converged?a.full.xyz:a.network_xyz)[i]||null}const p=paired();if(!p)return f.mono;const i=Math.round(f.t*motionInfo().fps),v=$('cameraMode').value;
    const xyz=(v==='dynamic'?p.rotational_xyz:p.fixed_xyz)[i];return xyz||null;
  }
  function refreshDynamicStatus(){
    const a=window.FRAME_CAL[data.id],mode=$('cameraMode').value;
    const states={PASS:a.physics_converged?'数值收敛 · 显示拟合后':'未收敛 · 显示拟合前',FAIL:'拟合失败 · 显示拟合前',RUNNING:'拟合中 · 显示拟合前'};
    $('fitStatus').textContent=mode==='redetect'?(states[a.physics_status]||a.physics_status):(paired()?.stage==='full'?'物理拟合后':'拟合前网络结果');
    $('dynamicStatus').textContent=mode==='redetect'?`A 机使用逐帧场线与相机参数：${a.valid.slice(Math.round(visibleStart(data)*a.fps)).filter(Boolean).length} / ${a.frames-Math.round(visibleStart(data)*a.fps)} 帧达到自动图像支持条件；红色十字由本帧识别的白线拟合。相机参数也已输入重建与物理拟合。${a.temporal_prior_frames?.length?` ${a.temporal_prior_frames.length} 帧受到遮挡，结合相邻帧约束后重新识别。`:''}`:'当前显示其他相机模式。';
    let distances=[];for(const f of data.frames){if(f.t<visibleStart(data))continue;const s=nearest(data.stereo,f.t+data.player_shifts.B,'t_B_s'),m=mono(f);if(s&&m&&s.xyz_m&&Math.abs(s.t_B_s-(f.t+data.player_shifts.B))<=.010&&m.every(Number.isFinite)&&s.xyz_m.every(Number.isFinite))distances.push(Math.hypot(...m.map((x,i)=>x-s.xyz_m[i])))}
    $('difference').textContent=distances.length?`${(distances.reduce((x,y)=>x+y,0)/distances.length).toFixed(2)} 米 · ${distances.length} 帧`:'暂无时间配对';
  }
  function ring(ctx,p,color,sourceWidth,k){if(!p||!p.every(Number.isFinite))return;const radius=Math.max(5,sourceWidth/110),line=Math.max(2,sourceWidth/320);
    ctx.strokeStyle=color;ctx.lineWidth=line;ctx.beginPath();ctx.arc(p[0],p[1],radius,0,2*Math.PI);ctx.stroke();dirty[k].push([p[0],p[1],radius+line+4]);
  }
  function paneVisible(k){return !expanded||expanded.dataset.view===k}
  function plotVisible(){return !expanded||expanded.dataset.view==='3D'}
  // In an enlarged video, its own presentation clock drives the controls.
  // Only that video is decoded; all three are caught up before returning.
  function masterKey(){return expanded&&'ABC'.includes(expanded.dataset.view)?expanded.dataset.view:'A'}
  function masterTime(){if(!data)return 0;const k=masterKey();return Math.max(visibleStart(data),Math.min(data.duration_s,videos[k].currentTime-data.player_shifts[k]))}
  function shouldRun(k){return !expanded||k===masterKey()}
  function overlay(k,t){
    const v=videos[k],c=overlays[k],court=courts[k];if(!v.videoWidth)return;c.dataset.presentationTime=String(t);
    const scale=Math.min(1,(c.clientWidth*(window.devicePixelRatio||1))/v.videoWidth,(c.clientHeight*(window.devicePixelRatio||1))/v.videoHeight);
    const width=Math.max(1,Math.round(v.videoWidth*scale)),height=Math.max(1,Math.round(v.videoHeight*scale));
    if(c.width!==width||c.height!==height||court.width!==width||court.height!==height){c.width=width;c.height=height;court.width=width;court.height=height;courtKeys[k]=null;dirty[k]=[]}
    const size=k==='C'&&$('cropC').checked&&data.C_crop_xywh?data.C_crop_xywh.slice(2):data.cameras[k]?.image_size||[v.videoWidth,v.videoHeight];const coordWidth=size[0],coordHeight=size[1],sx=c.width/coordWidth,sy=c.height/coordHeight,ctx=c.getContext('2d');ctx.setTransform(sx,0,0,sy,0,0);
    const mi=motionInfo(),a=window.FRAME_CAL[data.id],mode=$('cameraMode').value,frameKey=k==='A'?(mode==='dynamic'&&mi?frameIndex(t,mi):mode==='redetect'?calIndex(t,a):'fixed'):'fixed';
    const key=[data.id,k==='C'&&$('cropC').checked,$('showCourt').checked,$('showPoints').checked,$('showNet').checked,width,height,frameKey,mode].join('|');
    if(courtKeys[k]!==key){const cc=court.getContext('2d');cc.setTransform(sx,0,0,sy,0,0);cc.clearRect(0,0,coordWidth,coordHeight);
      if($('showCourt').checked&&data.cameras[k]){cc.strokeStyle='#20ddca';cc.lineWidth=Math.max(1.4,coordWidth/700);
        for(const [j,[p1,p2]] of lines.entries()){if(j>=groundCount&&!$('showNet').checked)continue;const u=mapped(k,framePoint(k,p1,t)),w=mapped(k,framePoint(k,p2,t));if(u&&w){cc.beginPath();cc.moveTo(...u);cc.lineTo(...w);cc.stroke()}}}
      if(k==='A'&&mode==='redetect'&&$('showPoints').checked){const i=calIndex(t,a);cc.strokeStyle='#fa424a';cc.lineWidth=Math.max(1.8,coordWidth/600);const r=Math.max(5,coordWidth/180);for(let j=0;j<a.points[i].length;j++){if(!a.point_valid[i][j])continue;const [x,y]=a.points[i][j];cc.beginPath();cc.moveTo(x-r,y);cc.lineTo(x+r,y);cc.moveTo(x,y-r);cc.lineTo(x,y+r);cc.stroke()}}
      courtKeys[k]=key;
    }
    for(const [x,y,r] of dirty[k])ctx.clearRect(x-r,y-r,2*r,2*r);dirty[k]=[];
    if(k==='A'){
      const f=nearest(data.frames,t);if(f&&Math.abs(f.t-t)<.04){const ball=mode==='redetect'?a.input_observations[calIndex(t,a)]:f.a;ring(ctx,ball,'#ffb224',coordWidth,k);if($('showProjection').checked)ring(ctx,framePoint('A',mono(f),t),'#47a5ff',coordWidth,k)}
    }else{const obs=data.observations[k],f=nearest(obs,t),tol=obs.length>1?Math.max(.006,Math.min(.025,(obs[1].t-obs[0].t)*.51+.001)):.012;if(f&&Math.abs(f.t-t)<=tol)ring(ctx,mapped(k,f.xy),'#13efa2',coordWidth,k)}
  }
  function draw3d(t){
    const canvas=$('plot'),ctx=canvas.getContext('2d'),w=canvas.width,h=canvas.height;ctx.clearRect(0,0,w,h);ctx.fillStyle='#f1f7f3';ctx.fillRect(0,0,w,h);
    const scale=36*Number($('zoom').value),cx=w/2,cy=h*.58;
    function xy(p){const X=Math.cos(yaw)*p[0]-Math.sin(yaw)*p[1],Y=Math.sin(yaw)*p[0]+Math.cos(yaw)*p[1];return[cx+X*scale,cy+(Y*Math.sin(pitch)-p[2]*Math.cos(pitch))*scale]}
    ctx.fillStyle='#dceee0';ctx.beginPath();outline.forEach((p,i)=>{const q=xy(p);i?ctx.lineTo(...q):ctx.moveTo(...q)});ctx.fill();
    ctx.strokeStyle='#90b3a1';ctx.lineWidth=2;for(const [a,b] of lines){ctx.beginPath();ctx.moveTo(...xy(a));ctx.lineTo(...xy(b));ctx.stroke()}
    const maxt=$('whole').checked?data.duration_s:t;
    ctx.setLineDash([]);ctx.strokeStyle='#236fc3';ctx.lineWidth=3;ctx.beginPath();let started=false;
    for(const f of data.frames){if(f.t<visibleStart(data))continue;if(f.t>maxt)break;const xyz=mono(f);if(!xyz||!xyz.every(Number.isFinite)){started=false;continue}const q=xy(xyz);if(started)ctx.lineTo(...q);else{ctx.moveTo(...q);started=true}}ctx.stroke();
    ctx.strokeStyle='#d9801f';ctx.lineWidth=3;ctx.setLineDash([9,7]);ctx.beginPath();let prev=null;
    for(const s of data.stereo){if(s.t_B_s-data.player_shifts.B<visibleStart(data))continue;if(s.t_B_s-data.player_shifts.B>maxt)break;if(!s.xyz_m||!s.xyz_m.every(Number.isFinite)){prev=null;continue}
      const q=xy(s.xyz_m);if(prev!==null&&s.t_B_s-prev<=.10&&!s.break_before)ctx.lineTo(...q);else ctx.moveTo(...q);prev=s.t_B_s}
    ctx.stroke();ctx.setLineDash([]);
    const f=nearest(data.frames,t);if(f&&mono(f)&&Math.abs(f.t-t)<.05){const q=xy(mono(f));ctx.fillStyle='#236fc3';ctx.beginPath();ctx.arc(q[0],q[1],7,0,2*Math.PI);ctx.fill()}
    const ref=nearest(data.stereo,t+data.player_shifts.B,'t_B_s');if(ref&&Math.abs(ref.t_B_s-(t+data.player_shifts.B))<=.010){const q=xy(ref.xyz_m);ctx.fillStyle='#d9801f';ctx.beginPath();ctx.arc(q[0],q[1],7,0,2*Math.PI);ctx.fill()}
    ctx.fillStyle='#698379';ctx.font='17px sans-serif';ctx.fillText('球场坐标（米）',24,h-18);
  }
  const fitName = {
    PHYSICS_CONVERGED:'物理拟合数值收敛',
    PHYSICS_NOT_CONVERGED_BEFORE_SHOWN:'未收敛 · 显示拟合前',
    PHYSICS_FAILED_BEFORE_SHOWN:'拟合异常 · 显示拟合前',
    PHYSICS_RUNNING_BEFORE_SHOWN:'拟合进行中 · 显示拟合前',
    NETWORK_MISSING:'暂无单目结果'
  };
  function pct(a,b){return b?Math.round(a*100/b)+'%':'—'}
  function choose(id){
    pause();data=byId[id];$('case').value=id;$('seek').min=visibleStart(data);$('seek').max=data.duration_s;$('seek').value=visibleStart(data);
    const s=data.stats,a=window.FRAME_CAL[id];
    $('caseNote').textContent=`${id} · ${visibleDuration(data).toFixed(2)} 秒 · A 原视频约 ${data.source_A_start_s.toFixed(1)} 秒起。`+(data.split_note?' 拆分位置为当前整理分界，尚非逐帧确认的击球事件。':'')+' '+data.input_cleanup;
    const startFrame=Math.round(visibleStart(data)*a.fps),shownA=a.input_observations.slice(startFrame);$('aCoverage').textContent=`A 机采用 ${shownA.filter(Boolean).length} / ${shownA.length} 帧球点；覆盖率并非准确率。`;
    const shownObs=k=>data.observations[k].filter(o=>o.t-data.player_shifts[k]>=visibleStart(data));const b=shownObs('B'),c=shownObs('C');$('bcCoverage').textContent=`B：${b.filter(o=>o.xy).length} / ${b.length} · C：${c.filter(o=>o.xy).length} / ${c.length}`;
    const stereoCount=data.stereo.filter(v=>v.t_B_s-data.player_shifts.B>=visibleStart(data)).length;$('bcNote').textContent=`本段 B/C 三维参考包含 ${stereoCount} 个配对结果。`;
    $('quality').textContent='';
    $('limits').textContent='按人工核对结果，B/C 轨迹作为近似三维真值；仍受同步、球点和标定误差影响，并非每帧都有参考。画面中的其他球仍会保留。';
    $('cropC').disabled=!data.C_crop_video;if(!data.C_crop_video)$('cropC').checked=false;
    const links=['A','B','C'].map(k=>`<a href="${data.videos[k]}">${k} 截取片段</a>`);if(data.C_crop_video)links.push(`<a href="${data.C_crop_video}">C 裁剪片段</a>`);
    $('files').innerHTML='素材：'+links.join(' · ');
    refreshDynamicStatus();loadSources(visibleStart(data));
  }
  function pause(){playbackEpoch++;resyncing=false;for(const v of Object.values(videos))v.pause();$('play').disabled=loading;$('play').textContent=loading?'加载中…':'播放'}
  function seekVideo(k,t){const v=videos[k];if(v.readyState>0&&Number.isFinite(v.duration)){const target=Math.max(0,Math.min(t+data.player_shifts[k],Math.max(0,v.duration-.001)));try{if(Math.abs(v.currentTime-target)>.001)v.currentTime=target}catch(e){}}}
  function updateControls(t){if(!data)return;t=Math.max(visibleStart(data),Math.min(data.duration_s,t));$('clock').textContent=`${(t-visibleStart(data)).toFixed(2)} / ${visibleDuration(data).toFixed(2)} 秒`;$('seek').value=t}
  function refresh(t){if(!data)return;
    for(const k of 'ABC')if(paneVisible(k)&&videos[k].readyState>=2)overlay(k,displayed[k]===null?videos[k].currentTime:displayed[k]);
    if(plotVisible())draw3d(displayed.A===null?t:displayed.A);updateControls(t);
  }
  function setTime(t){t=Math.max(visibleStart(data),Math.min(data.duration_s,t));for(const k of 'ABC')if(shouldRun(k))seekVideo(k,t);updateControls(t)}
  function updateActivity(t=masterTime(),wasPlaying=!videos[masterKey()].paused){if(!data)return;
    for(const k of 'ABC'){const v=videos[k];if(!shouldRun(k)){v.pause();continue}
      const target=Math.max(0,Math.min(t+data.player_shifts[k],Math.max(0,(v.duration||0)-.001)));
      if(v.readyState>0&&Math.abs(v.currentTime-target)>.01)seekVideo(k,t);
      if(wasPlaying&&v.paused)v.play().catch(()=>{});
    }
    refresh(t);
  }
  function waitForSeek(k,t){const v=videos[k];if(v.readyState===0)return Promise.resolve();
    return new Promise(resolve=>{let done=false,timer;const finish=()=>{if(done)return;done=true;clearTimeout(timer);v.removeEventListener('seeked',finish);resolve()};
      v.addEventListener('seeked',finish);timer=setTimeout(finish,2000);seekVideo(k,t);if(!v.seeking)finish();
    });
  }
  async function resumeAligned(t){
    const token=++playbackEpoch;resyncing=true;const active='ABC'.split('').filter(shouldRun);
    for(const v of Object.values(videos))v.pause();$('play').disabled=true;$('play').textContent='同步中…';
    try{
      await Promise.all(active.map(k=>waitForSeek(k,t)));if(token!==playbackEpoch)return;
      for(const k of active)videos[k].playbackRate=Number($('rate').value);
      await Promise.all(active.map(k=>videos[k].play()));if(token!==playbackEpoch)return;
      $('play').textContent='暂停';
    }catch(e){if(token===playbackEpoch){pause();$('caseNote').textContent+=' 播放未能开始，请重试。'}}
    finally{if(token===playbackEpoch){resyncing=false;$('play').disabled=false}}
  }
  function waitUntilReady(k,t,version){const v=videos[k];
    return new Promise(resolve=>{let done=false,timer;const names=['loadedmetadata','loadeddata','canplay','seeked','error'];
      const finish=ok=>{if(done)return;done=true;clearTimeout(timer);for(const n of names)v.removeEventListener(n,check);resolve(ok)};
      const check=()=>{if(version!==loadVersion)return finish(false);if(v.error)return finish(false);if(v.readyState<1||v.seeking)return;
        const target=Math.max(0,Math.min(t+data.player_shifts[k],Math.max(0,(v.duration||0)-.001)));
        if(Math.abs(v.currentTime-target)>.025){seekVideo(k,t);return}if(v.readyState>=2)finish(true)};
      for(const n of names)v.addEventListener(n,check);timer=setTimeout(()=>finish(false),12000);check();
    });
  }
  async function loadSources(t){
    const version=++loadVersion;loading=true;$('play').disabled=true;$('play').textContent='加载中…';const pending=[];
    for(const k of 'ABC'){
      displayed[k]=null;courtKeys[k]=null;dirty[k]=[];for(const canvas of [overlays[k],courts[k]]){const ctx=canvas.getContext('2d');ctx.setTransform(1,0,0,1,0,0);ctx.clearRect(0,0,canvas.width,canvas.height)}
      const v=videos[k];v.preload='auto';v.onloadedmetadata=()=>{if(version!==loadVersion)return;seekVideo(k,t);refresh(t)};
      const light=data.id==='case01_A0'&&(k==='B'||k==='C')?`media/curated_20261116/materials/case01_A0/${k}_preview.mp4`:null;
      v.src=k==='C'&&$('cropC').checked?data.C_crop_video:(light||data.videos[k]);v.load();pending.push(waitUntilReady(k,t,version));
    }
    refresh(t);const ready=await Promise.all(pending);if(version!==loadVersion)return;loading=false;$('play').disabled=false;$('play').textContent='播放';
    if(ready.some(x=>!x))$('caseNote').textContent+=' 有画面加载较慢，请稍候或重试。';refresh(t);
  }
  $('play').onclick=async()=>{
    if(loading||resyncing)return;const v=videos[masterKey()];
    if(!v.paused){pause();return}
    let t=masterTime();if(v.ended||t>=data.duration_s-.04)t=visibleStart(data);
    await resumeAligned(t);
  };
  $('back').onclick=()=>{const t=masterTime();pause();setTime(t-1/30)};$('next').onclick=()=>{const t=masterTime();pause();setTime(t+1/30)};$('reset').onclick=()=>{pause();setTime(visibleStart(data))};
  $('seek').oninput=e=>{pause();setTime(Number(e.target.value))};$('rate').onchange=()=>Object.values(videos).forEach(v=>v.playbackRate=Number($('rate').value));
  $('case').onchange=e=>choose(e.target.value);$('cropC').onchange=()=>{const t=masterTime();pause();loadSources(t)};
  $('cameraMode').onchange=()=>{courtKeys.A=null;refreshDynamicStatus();refresh(masterTime())};
  $('showCourt').onchange=$('showPoints').onchange=$('showNet').onchange=$('showProjection').onchange=$('whole').onchange=$('zoom').oninput=()=>refresh(masterTime());
  window.addEventListener('resize',()=>{if(data)refresh(masterTime())});
  $('resetView').onclick=()=>{yaw=-.62;pitch=.80;$('zoom').value=1;refresh(masterTime())};
  const plot=$('plot');
  plot.onpointerdown=e=>{drag={x:e.clientX,y:e.clientY,startX:e.clientX,startY:e.clientY,moved:false};plot.setPointerCapture(e.pointerId)};
  plot.onpointerup=()=>{if(drag&&drag.moved){suppressPlotClick=true;setTimeout(()=>{suppressPlotClick=false},0)}drag=null};
  plot.onpointercancel=()=>{drag=null};
  plot.onpointermove=e=>{if(drag){
    if(Math.hypot(e.clientX-drag.startX,e.clientY-drag.startY)>5)drag.moved=true;
    if(drag.moved){yaw+=(e.clientX-drag.x)*.008;pitch=Math.max(.15,Math.min(1.5,pitch+(e.clientY-drag.y)*.008));draw3d(displayed.A===null?videos.A.currentTime:displayed.A)}
    drag.x=e.clientX;drag.y=e.clientY;
  }};
  function closeExpanded(){
    if(!expanded)return;const t=masterTime(),wasPlaying=!videos[masterKey()].paused,button=expanded.querySelector('.expand-btn');expanded.classList.remove('expanded');
    button.textContent='⤢';button.setAttribute('aria-expanded','false');button.setAttribute('aria-label',`放大${expanded.dataset.view==='3D'?'三维轨迹':expanded.dataset.view+' 机画面'}`);button.title='放大画面';
    expanded=null;document.body.classList.remove('view-expanded');$('expandBackdrop').hidden=true;$('expandToolbar').hidden=true;
    refresh(t);if(wasPlaying)resumeAligned(t);else updateActivity(t,false);button.focus({preventScroll:true});
  }
  function expandView(view){
    if(expanded===view){closeExpanded();return}if(resyncing)pause();const t=masterTime(),wasPlaying=!videos[masterKey()].paused;if(expanded)closeExpanded();expanded=view;
    view.classList.add('expanded');document.body.classList.add('view-expanded');$('expandBackdrop').hidden=false;$('expandToolbar').hidden=false;
    const button=view.querySelector('.expand-btn');button.textContent='退出';button.setAttribute('aria-expanded','true');button.setAttribute('aria-label','退出放大');button.title='退出放大';updateActivity(t,wasPlaying);button.focus({preventScroll:true});
  }
  document.querySelectorAll('.view').forEach(view=>{
    view.querySelector('.expand-btn').addEventListener('click',e=>{e.stopPropagation();expandView(view)});
    view.addEventListener('click',e=>{if(expanded||e.target.closest('button')||(view.classList.contains('plot-view')&&suppressPlotClick))return;expandView(view)});
  });
  $('expandBackdrop').addEventListener('click',closeExpanded);
  document.addEventListener('keydown',e=>{if(e.key==='Escape'&&expanded){e.preventDefault();closeExpanded()}});
  function seconds(x){return x==null?'未单独计时':x>=60?`${Math.floor(x/60)} 分 ${(x%60).toFixed(1)} 秒`:`${x.toFixed(2)} 秒`}
  for(const c of cases){const o=document.createElement('option');o.value=c.id;o.textContent=`${c.id} · ${visibleDuration(c).toFixed(1)} 秒`; $('case').appendChild(o);
    const tr=document.createElement('tr'),a=window.FRAME_CAL[c.id];
    const phys=a.physics_status==='RUNNING'?'进行中':a.physics_status==='FAIL'?'失败，显示拟合前':a.physics_converged?'收敛':'未收敛，显示拟合前';
    const gap=c.paired_gap,total=a.calibration_seconds==null||a.detector_benchmark_seconds==null?null:a.calibration_seconds+a.detector_benchmark_seconds+a.total_stage_seconds;const values=[c.id,visibleDuration(c).toFixed(1)+' 秒',seconds(total),seconds(a.total_stage_seconds),`${seconds(a.detector_benchmark_seconds)} / ${seconds(a.network_seconds)}`,`${seconds(a.physics_seconds)} · ${phys}`,seconds(a.calibration_seconds),gap.frames?`${gap.mean_m.toFixed(2)} 米 / ${gap.frames} 帧`:'暂无配对',c.split_note?'已整理 · 分界待确认':'已整理'];
    values.forEach((value,i)=>{const td=document.createElement('td');if(i===0){const b=document.createElement('button');b.className='case-link';b.textContent=value;b.onclick=()=>{choose(c.id);window.scrollTo({top:0,behavior:'smooth'})};td.appendChild(b)}else td.textContent=value;tr.appendChild(td)});$('caseRows').appendChild(tr);
  }
  function met(v){return v==null?'—':v.toFixed(2)}
  for(const c of cases){const m=c.real_metrics,tr=document.createElement('tr');
    const vals=[c.id+(c.reference_protocol.startsWith('A观测')?' †':''),`${m.frames} / ${m.total_frames}`,`${(m.coverage*100).toFixed(1)}%`,met(m.network_mean_m),met(m.mean_m),met(m.median_m),met(m.p95_m),met(m.rms_m)];
    vals.forEach((value,i)=>{const td=document.createElement('td');if(i===0){const b=document.createElement('button');b.className='case-link';b.textContent=value;b.onclick=()=>{choose(c.id);window.scrollTo({top:0,behavior:'smooth'})};td.appendChild(b)}else td.textContent=value;tr.appendChild(td)});$('realResultsRows').appendChild(tr);
  }
  // Draw a circle for the actual presented frame rather than the playback
  // clock, which can lead or lag a frame when decoding is under load.
  function presented(k,mediaTime,now){if(!data||!Number.isFinite(mediaTime))return;displayed[k]=mediaTime;
    if(paneVisible(k))overlay(k,mediaTime);
    if(k===masterKey()){const t=mediaTime-data.player_shifts[k];if(plotVisible())draw3d(t);if(now-lastControlsUpdate>=100){updateControls(t);lastControlsUpdate=now}}
  }
  for(const k of 'ABC'){
    const v=videos[k];
    if(frameCallback[k]){const next=(now,meta)=>{v.requestVideoFrameCallback(next);presented(k,meta.mediaTime,now)};v.requestVideoFrameCallback(next)}
    else for(const event of ['loadeddata','seeked'])v.addEventListener(event,()=>presented(k,v.currentTime,performance.now()));
  }
  // Old browsers lack presented-frame callbacks. Keep a lighter fallback.
  if(Object.values(frameCallback).some(x=>!x)){
    function fallback(now){for(const k of 'ABC')if(!frameCallback[k]&&!videos[k].paused&&shouldRun(k)&&videos[k].readyState>=2)presented(k,videos[k].currentTime,now);requestAnimationFrame(fallback)}
    requestAnimationFrame(fallback);
  }
  function syncTick(){if(!data||loading||resyncing||videos[masterKey()].paused)return;const t=masterTime();
    if(t>=data.duration_s-.005){pause();setTime(data.duration_s);return}
    if(expanded)return;
    const now=performance.now();for(const k of 'BC'){const v=videos[k];if(!shouldRun(k)||v.paused||v.seeking||v.readyState<2||now-lastCorrection[k]<700)continue;
      const target=Math.max(0,Math.min(t+data.player_shifts[k],Math.max(0,(v.duration||0)-.001)));
      if(Math.abs(v.currentTime-target)>.06){lastCorrection[k]=now;seekVideo(k,t)}
    }
  }
  for(const k of 'ABC')videos[k].addEventListener('ended',()=>{if(data&&!loading&&!resyncing&&k===masterKey()&&videos[k].ended&&masterTime()>=data.duration_s-.04){pause();setTime(data.duration_s)}});
  choose(cases[0].id);setInterval(syncTick,250);
})();
