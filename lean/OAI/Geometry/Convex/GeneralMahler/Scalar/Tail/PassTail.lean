import OAI.Geometry.Convex.GeneralMahler.Scalar.Tail.Coords

namespace OAI
/-! Uniform global (after 64) certificates of value and Euler derivative bounds. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail
open JT JTB Grid Jet Tag Cert Cert.IV Profile Layers
-- K needs individual scaled-error bounds because tends to zero
private lemma checkKR: SubB (bKR 0) (band (-500) 500) &&
    SubB (bKR 1) (band (-5000) 5000) &&
    SubB (bKR 2) (band (-15000) 15000) := by decide +kernel

lemma kTail {y:ℝ} (h:y0≤ y) :
    Kp (XX y) ∈ band 0 8 ∧ Kp (XX y) ≤ ev y*y ∧ 0≤ kF y 2-kF y 1 := by
  have hk:Kp (XX y)=ev y*(Lv y+KR y 0-3/2) := by
    rw [← kF0]
    change Wv y +IJ y 0* _= _
    rw [IJ0]; unfold Wv; dsimp [Jet.subJ,Jet.ray]; ring
  have hi := checkKR
  simp only [Bool.and_eq_true] at hi
  have he:= subB (fKR h 0) hi.1.1; have hp:=subB (fKR h 1) hi.1.2
  have hj:=subB (fKR h 2) hi.2
  rw [mem_band] at he hp hj
  norm_num at he hp hj
  have hv:= iP y
  have hl:= econ h
  have hs:= (vsmall h).2.2
  refine ⟨?_,?_,?_⟩
  · rw [mem_band,hk]
    norm_num
    constructor
    · exact mul_nonneg hv.le (by linarith [he.1,hl.1])
    nlinarith [he.2,hl.2.2]
  · rw [hk]
    apply mul_le_mul_of_nonneg_left _ hv.le
    unfold Lv; linarith [he.2,ro_lim.2.2.2]
  have hz : kF y 2-kF y 1 = ev y * (6* (Lv y+KR y 0-3/2)-5-5*KR y 1+KR y 2) := by
    -- use WW coeff recurrence at k
    simp only [kF,plusJ,WW,Wrec,mulJ,mulJ0,IJ,subJ,tail,ray,Wv]; ring
  rw [hz]
  apply mul_nonneg hv.le; linarith [hl.1,he.1,hp.2,hj.1]

-- profiles v' correction and v''
def ivb:IV:= IV.span 0 ((1:IV)/IV.c 64)
def mxB:=pf0/(bPP 0)
def rvb:IV:= mxB - ivb*(bnJ 0)/(bmJ 0)
def vvb:IV:= 2-mxB-mxB*mxB-(bnJ 0)/sq (bmJ 0)
lemma vTail {y:ℝ}(h:y0≤y): deriv Profile.v (XX y)-XX y∈rvb ∧
    deriv (deriv Profile.v) (XX y)∈vvb := by
  let v:=MJ y 0; let n:=NJ y 0; let x:=XX y
  have he:=ym_id y
  have hi:sY x=iv y*v := by unfold x v iv; rw [← ym_id]; have ht:=xP y; field_simp
  have hp:sB x= (iv y)^2*n:= (n_id y).symm
  have hX:=xP y; have hY:= vP y; have hV:0 < v:=MPv _
  let A:=sP x
  have hP:A ∈ bPP 0 := by rw [show A=PP y 0 from (P0 y).symm];apply fPP h
  have hh:phi x∈pf0 := by
    have he := lpF h 0 0
    change Qp 0 y∈pr 0 0 at he
    simpa only [Qp,pow_zero,one_mul,pr, show 0≤(10:ℕ) from by decide, ite_eq_left] using he
  have hz:x*phi x∈pf0 := by
    have he:=lpF h 1 0
    change Qp 1 y ∈ pr 0 1 at he
    simpa only [Qp,pow_one,pr, show (1:ℕ)≤10 from by decide,ite_eq_left] using he
  have hv:v∈bmJ 0:=fmJ h _
  have hn:n∈ bnJ 0:=fnJ h _
  have hb:iv y∈ivb := span_conv mz (mdiv mo (show (64:ℝ)∈ c 64 from mc 64))
    hY.le (vsmall h).2.1
  have hx:=mdiv hh hP
  change deriv _ x-x∈_∧ deriv _ x∈_
  rw [← rv_stable, ← v2_stable]
  unfold sRv sV2; rw [hp,hi]
  change phi x/A-(iv y)^2*n/(iv y*v)∈_∧2-phi x/A*(x+phi x/A)-
    _∈_
  rw [show (iv y)^2*n/(iv y*v)=iv y*n/v from by field_simp,
    show phi x/A*(x+phi x/A)=x*phi x/A+phi x/A*(phi x/A) by ring]
  refine ⟨msub hx (mdiv (mmul hb hn) hv),?_⟩
  rw [show iv y ^2*n/(iv y*v*(iv y*v))=n/v^2 from by field_simp,sub_add_eq_sub_sub]
  exact msub (msub (msub mtwo (mdiv hz hP)) (mmul hx hx)) (mdiv hn (msq hv))

def tabT : Tag→ IV
  | R=> bRj 0
  | K=> band 0 8
  | C=> bcF 0
  | Q=> bQj 0
  | dK=>ba bkF
  | dC=>ba bcF
  | dQ=>ba bQj
  | ddK=>bdN bkF
  | ddC=>bdN bcF
  | ddQ=>bdN bQj
  | NK=>clampNN (bbN bkF)
  | NC=>bbN bcF
  | NQ=>bbN bQj
  | RV=>rvb
  | V=>vvb
  | S=>bS2 bQj

lemma tag_tail {x y:ℝ} (h:y0 ≤ y) (he:xs x=XX y) (hR:CJet.RadH) (hf:TestF qu)
    (t:Tag) : t.act x∈tabT t := by
  unfold tabT
  generalize hQ : bQj = A
  have hmQ : Fits (ql y) A := hQ ▸ mQl h
  obtain ⟨ha,hb,hc,_⟩:=mDots he h TkF Profile.testK kF0 (fkF h)
  obtain ⟨hK,hK',hN⟩:=kTail h
  have hN':0 ≤ NNf Kp x := by
    have hh:= (dots_log he TkF Profile.testK kF0).2.1
    rw [hh]; exact mul_nonneg (sq_nonneg _) hN
  obtain ⟨hd,hi,hj,_⟩:=mDots he h TcF Profile.testC cF0 (fcF h)
  obtain ⟨hp,hq,hu,ht⟩:=mDots he h (Twq hR) hf qe0 hmQ
  have hr:=mRj h 0
  have hcv:=fcF h 0
  have hqv:=hmQ 0
  obtain ⟨hx,hv⟩:=vTail h
  rw [rre0] at hr; rw [cF0] at hcv; rw [qe0] at hqv
  rw [← he] at hK hcv hqv hx hv hr
  cases t
  · exact hr
  · exact hK
  · exact hcv
  · exact hqv
  · exact ha
  · exact hd
  · exact hp
  · exact hc
  · exact hj
  · exact hu
  · exact mclamp hb hN'
  · exact hi
  · exact hq
  · exact hx
  · exact hv
  · exact ht

theorem tailCheck: pass0 719 tabT=true := by decide +kernel
theorem tailXCheck: SubB (tabT C) (band (-5002) (-4998)) &&
    SubB (tabT Q) (band 2550 2556) := by decide +kernel

lemma rad_tail {x y:ℝ} (h:y0≤y) (he:xs x=XX y): Tag.R.act x∈rng R := by
  have hi : rrF y 0∈bRj 0:= mRj h 0
  have hu : R.act x=rrF y 0:= by
    rw [rre0, ← he]
    rfl
  have hh := tailCheck
  simp only [pass0,Bool.and_eq_true] at hh
  rw [hu]
  apply subB hi (hasSub hh.1.1.1.1 R)
end GeneralMahler.SCal.Tail

end OAI
