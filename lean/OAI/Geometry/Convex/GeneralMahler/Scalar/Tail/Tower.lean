import OAI.Geometry.Convex.GeneralMahler.Scalar.Tail.Base

namespace OAI
/-! §07 tail profile identities using normalized log towers. -/
open Set Filter Real
open scoped Topology
noncomputable section
namespace GeneralMahler.SCal.Tail.JT
open Profile Layers Jet
variable (x:ℝ) -- logarithmic point

def MJ:= TM 0 0
def NJ:= TM 1 0
def Pt (x:ℝ):= mulJ (TP 1 x) (MJ x)
def U (x:ℝ):= mulJ (IJ x) (Pt x)
def PP (x:ℝ):=subJ (ray 1) (U x)
def PQ (x:ℝ):= mulJ (PP x) (PP x)
def HH (x:ℝ):=compJ (hfRF (U x 0)) (U x)
def H1 (x:ℝ):=compJ (tail (hfRF (U x 0))) (U x)
def DH (x:ℝ):=mulJ (mulJ (ray (1/2)) (Pt x)) (subJ (invSub vn (PP x)) (H1 x))
def M2 (x:ℝ):=mulJ (MJ x) (MJ x)
def NN (x:ℝ):=mulJ (NJ x) (NJ x)
def del (x:ℝ):=plusJ (subJ (negJ (logSub vn (MJ x) (Real.log (MJ x 0)))) (subJ (PP x) (ray 1)))
  (subJ (mulJ (PQ x) (HH x)) (ray (1/2)))
def wZ (x:ℝ):=plusJ (WW x) (mulJ (IJ x) (del x))
def A (x:ℝ):=subJ (mulJ (ray (1/2)) (NN x))
  (mulJ (mulJ (mulJ (ray 2) (PP x)) (HH x)) (NJ x))
def mi (x:ℝ):= mulJ (NJ x) (plusJ (ray 1) (MJ x))
def N1 (x:ℝ):= mulJ (IJ x) (NN x)
def DD (x:ℝ):= plusJ (plusJ (DH x) (A x)) (mulJ (NN x) (wZ x))
def G0 (x:ℝ):= subJ (mulJ (mulJ (ray (1/4)) (IJ x)) (mi x))
  (mulJ (mulJ (ray (1/2)) (M2 x)) (wZ x))
def KR (x:ℝ):=
  plusJ (plusJ (plusJ (plusJ (subJ (plusJ (DH x) (A x)) (NJ x))
    (mulJ (ray (1/2)) (N1 x))) (ray (3/2)))
    (mulJ (plusJ (M2 x) (N1 x)) (del x)))
    (mulJ (subJ (NN x) (mi x)) (WW x))
def CQ (x:ℝ):= subJ (mulJ (ray (ar-1)) (subJ (tail (tail (G0 x))) (tail (G0 x)))) (DD x)
def dF (x:ℝ):= plusJ (ray (1/2)) (mulJ (IJ x) (DD x))
def kF (x:ℝ):= plusJ (WW x) (mulJ (IJ x) (subJ (KR x) (ray (3/2))))
def gF (x:ℝ):= plusJ (G0 x) (ray (1/4))
def cF (x:ℝ):= subJ (mulJ (IJ x) (CQ x)) (ray (1/2))

lemma ym_id : sY (XX x) * XX x=MJ x 0 := by rw [MJ,TM0]; unfold sY Mk; ring
lemma n_id : ev x * NJ x 0=sB (XX x) := by
  rw [NJ,TM0]; unfold ev iv sB Mk; have he:=xP x; field_simp
lemma pt0 : Pt x 0=XX x*phi (XX x)*MJ x 0:=by
  change (XX x ^1*phi (XX x))*_=_
  rw [pow_one]
lemma U0 : U x 0=sU (XX x):=by
  change IJ x 0*Pt x 0=_
  rw [IJ0,pt0, ← ym_id]
  have he:=xP x; unfold ev iv sU; field_simp
lemma MPv : 0 < MJ x 0:= by rw [MJ,TM0]; apply MkP
lemma Nv : 0 < NJ x 0:= by rw [NJ,TM0]; apply MkP
lemma mi_id : ev x * mi x 0= 1 - (MJ x 0)^2 := by
  change ev x * (NJ x 0 *(1+MJ x 0))=_
  rw [NJ,MJ,TM0,TM0,M0e]; ring
lemma P0 : PP x 0=sP (XX x):= by change 1-U x 0=_; rw [U0];rfl
lemma H0 : HH x 0=sH (XX x):= by
  change Nat.factorial 0*Qh 0 (U x 0)=_
  rw [U0]; unfold sH; simp

lemma ht1 (u:ℝ) (hu:0<u) (hv:u<1):
    Qh 0 u-1/2=u/2*((1-u)⁻¹-Qh 1 u) := by
  let f:=fun u:ℝ=>u^2*Qh 0 u
  have he:= ((hasDerivAt_id' u).pow 2).fun_mul (hdQ 0 hv)
  let g:= fun u:ℝ=> -Real.log (1-u)-u
  have h:= ((((hasDerivAt_id' u).const_sub 1).log (sub_pos.mpr hv).ne').neg.sub (hasDerivAt_id' u))
  have he' : f =ᶠ[𝓝 u] g := by
    filter_upwards [Ioo_mem_nhds hu hv] with x hx
    exact hlog hx.1 hx.2
  have hf : HasDerivAt f _ u := he
  have hg : HasDerivAt g _ u := h
  have hj:= hf.unique (hg.congr_of_eventuallyEq he')
  norm_num at hj
  have hp : 0<1-u := by linarith
  field_simp at hj ⊢
  nlinarith

lemma DH0 : ev x*DH x 0 = HH x 0-1/2 := by
  let y:=sU (XX x)
  change ev x*((1/2*Pt x 0)*((PP x 0)⁻¹-_))=_
  have h : HH x 0=Qh 0 y := H0 x
  have he : PP x 0=1-y:= P0 x
  have hz : H1 x 0=Qh 1 y := by
    change (Nat.factorial _ : ℝ)*Qh 1 (U x 0)= _
    rw [U0]; unfold y; norm_num
  rw [h,he,hz,ht1 y (u_pos _) (u_le _)]
  have hp : ev x *Pt x 0=y := by rw [← IJ0]; exact U0 x
  rw [← hp]; ring
lemma WZ0 :
    wZ x 0= ev x*(sJ (XX x) -(XX x *XX x)/2+(PP x 0)^2*(HH x 0)) := by
  have hm : Real.log (MJ x 0)=Real.log (sY (XX x))+x := by
    rw [← ym_id, Real.log_mul (show sY (XX x)≠0 from (Ymp _ _).ne') (xP _).ne']
    unfold XX; simp
  change Wv x+ IJ x 0*((-Real.log (MJ x 0)-(PP x 0-1))+
    (PP x 0*PP x 0*HH x 0-1/2))=_
  rw [hm,IJ0,P0]; unfold Wv Lv Z0 sJ; ring

lemma dF0 : dF x 0 = d (XX x) := by
  change 1/2+IJ x 0*(DH x 0+(1/2*(NJ x 0*NJ x 0)-2*PP x 0*HH x 0*NJ x 0)+
    NJ x 0*NJ x 0*wZ x 0)=_
  have hi : ev x*(XX x*XX x)=1:= by unfold ev iv; have hp:=xP x; field_simp
  rw [IJ0, mul_add,mul_add,DH0,WZ0,← d_stable]
  unfold sd sW
  rw [← H0,← n_id, ← P0]
  linear_combination (ev x*(NJ x 0 ^2)/(-2))*hi

lemma gF0 : gF x 0=g (XX x) := by
  change 1/4*IJ x 0 * mi x 0- (1/2*(MJ x 0*MJ x 0)*wZ x 0)+1/4=_
  rw [IJ0,mul_assoc (1/4:ℝ),mi_id,WZ0]
  have he (x:ℝ) : g x= (1 - (sY x)^2*(j x+(sP x)^2*sH x))/2 := by
    unfold g; rw [h_f]
    have hh : X x ^ 2*(sU x ^ 2*sH x)=(sP x*sY x)^2*sH x:=by rw [← Xu]; ring
    rw [hh]; unfold sY; rw [Ym0]; ring
  rw [he,H0,P0,lp_st, ← ym_id]
  have hp := xP x; unfold ev iv; field_simp; ring

lemma kF0 : kF x 0=Kp (XX x) := by
  rw [Kp,← gF0,← dF0]
  let t:=IJ x 0; let z:=mi x 0; let m:= M2 x 0; let n:= NJ x 0
  have he : NN x 0=n*n := rfl
  have hf : t*z=1-m := by unfold t m; rw [IJ0,mi_id]; change 1-_=1-MJ x 0*MJ x 0;rw [pow_two]
  have hh : z = n*(2-t*n) := by
    have hi : MJ x 0=1-t*n := by unfold t n; rw [MJ,NJ,TM0,TM0,IJ0,M0e]
    change n*(1+MJ x 0)=_; rw [hi]; ring
  let a:= A x 0; let b:= DH x 0; let w:= Wv x; let d:= del x 0
  change w+t*((b+a-n+1/2*(t*NN x 0)+3/2+(m+t*NN x 0)*d+(NN x 0-z)*w)-3/2)=
    1/2+t*(b+a+NN x 0*(w+t*d))-2*(1/4*t*z-1/2*m*(w+t*d)+1/4)
  rw [he]; rw [show m=1-t*z from by linarith]; rw [hh];ring

lemma TeM:TW univ MJ:=Tm 0 0
lemma TeN:TW univ NJ:=Tm 1 0
lemma TeP:TW univ Pt:=(Tp _).mul TeM
lemma TeU:TW univ U:=Ti.mul TeP
lemma TePP:TW univ PP:=(TW.const _).sub TeU
lemma huJ : ∀ x:ℝ,U x 0∈Iio 1:=fun x=>by rw [U0]; exact u_le _
lemma ppj (x):0 < PP x 0:=by rw [P0,sPe]; apply p_pos
lemma TeH: TW univ HH:=TeU.comp Ihf fun x _=> huJ x
lemma TeH1: TW univ H1:=TeU.comp Ihf.tail fun x _=> huJ x
lemma Ted: TW univ del:=
  (((TeM.log (fun x _=> (MPv x).ne')).neg.sub (TePP.sub (TW.const _))).add
    (((TePP.mul TePP).mul TeH).sub (TW.const _)))
lemma TeZ: TW univ wZ:= Tw.add (Ti.mul Ted)
lemma Tem2:TW univ M2:=TeM.mul TeM
lemma Ten2:TW univ NN:=TeN.mul TeN
lemma Temi:TW univ mi:=TeN.mul ((TW.const _).add TeM)
lemma TeG:TW univ G0:=
  (((TW.const _).mul Ti).mul Temi).sub (((TW.const _).mul Tem2).mul TeZ)
lemma TeA:TW univ A:= ((TW.const _).mul Ten2).sub ((((TW.const _).mul TePP).mul TeH).mul TeN)
lemma TeDH : TW univ DH:=
  ((TW.const _).mul TeP).mul ((TePP.inv (fun x _=>(ppj x).ne')).sub TeH1)
lemma TeDD : TW univ DD:= (TeDH.add TeA).add (Ten2.mul TeZ)
lemma TeN1:TW univ N1:=Ti.mul Ten2
lemma TeKR:TW univ KR:=
  ((((((TeDH.add TeA).sub TeN).add ((TW.const _).mul TeN1)).add (TW.const _)).add
    ((Tem2.add TeN1).mul Ted)).add ((Ten2.sub Temi).mul Tw))
lemma TeCQ:TW univ CQ:= ((TW.const _).mul (TeG.tail.tail.sub TeG.tail)).sub TeDD
lemma TdF:TW univ dF:= (TW.const _).add (Ti.mul TeDD)
lemma TkF:TW univ kF:=Tw.add (Ti.mul (TeKR.sub (TW.const _)))
lemma TgF:TW univ gF:=TeG.add (TW.const _)
lemma TcF:TW univ cF:=(Ti.mul TeCQ).sub (TW.const _)

lemma path (f:ℝ→ℝ) (hf:TestF f) (F:RF) (he:TW univ F) (hh:∀ x,F x 0=f (XX x)):
    F x 1=XX x*deriv f (XX x)∧
      F x 2=F x 1+ XX x*XX x*deriv (deriv f) (XX x) := by
  have hi (g:ℝ→ℝ) (hg:TestF g) (x:ℝ): HasDerivAt (fun x=>g (XX x)) (deriv g (XX x)* XX x) x :=
    (hg.diff _).hasDerivAt.comp x (Xd0 x)
  have h₁ (x:ℝ) : F x 1=XX x *deriv f (XX x) := by
    have he := he 0 x (mem_univ _)
    simp_rw [hh] at he
    rw [show F x 1=_ from he.unique (hi f hf x)]
    ring
  refine ⟨h₁ x,?_⟩
  have ht := he 1 x (mem_univ _)
  simp_rw [h₁] at ht
  rw [show F x 2=_ from ht.unique ((Xd0 x).fun_mul (hi (deriv f) hf.der x)),h₁]
  ring

lemma cF0 : cF x 0=Cp (XX x) := by
  obtain ⟨h,h₁⟩:=path x g g_test gF TgF gF0
  have hp := xP x
  have he : ev x*(gF x 2-gF x 1)=deriv (deriv g) (XX x) := by rw [h₁]; unfold ev iv; field_simp; ring
  have hi : ev x*(G0 x 2-G0 x 1)=deriv (deriv g) (XX x) := by
    change ev x*((G0 x 2+0)-(G0 x 1+0))=_ at he; simpa using he
  rw [Cp,← dF0,← hi]
  change IJ x 0*((ar-1)*(G0 x 2-G0 x 1)-DD x 0)-1/2= -(1/2+IJ x 0*DD x 0)+_
  rw [IJ0]; ring
end GeneralMahler.SCal.Tail.JT

end

end OAI
