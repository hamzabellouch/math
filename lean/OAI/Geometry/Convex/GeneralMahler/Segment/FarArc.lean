import OAI.Geometry.Convex.GeneralMahler.Segment.Small

namespace OAI
/-! Angular bounds in tail cases. -/
noncomputable section
open Set Filter Real MeasureTheory
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Jet Segment
local notation "w" => Profile.omegaP
variable {h:ℝ}
lemma arcBound (m:ℝ) (hh:0<h) (C U V:ℝ)
    (hc:cott h ≤ C)
    (hu:0≤U)(hv:0≤V)
    (he:1+w^2*C^2≤U^2) (hf:C^2+w^2≤ V^2) :
    let k:ℝ:=1+w^2
    let s:=2*r^2
    s*(1-(1+U)/(2*k))≤ Pastar h ∧
    Pastar h ≤ s*(1-(1-U)/(2*k)) ∧
    |Pdstar m h| ≤ s*((C+V)/(2*k)):=by
  intro k s
  let u:=cos (w*h); let v:=sin (w*h)
  have hp : 0 < cott h:= div_pos (cosh_pos _) (sinh_pos_iff.mpr hh)
  have h1 : u^2+v^2=1:=by rw [add_comm]; exact Real.sin_sq_add_cos_sq _
  let x:=u^2-v^2; let y:=2*u*v
  have h2:x^2+y^2=1 := by
    rw [show x^2+y^2=(u^2+v^2)^2 by unfold x y; ring,h1];ring
  have HK:0<k := by unfold k;positivity
  have hs:0 ≤ s:=by unfold s; positivity
  have ht:|x+w*cott h*y|≤U:=by
    have hz:1^2+(w*cott h)^2≤U^2:=by
      apply le_trans _ he; rw [mul_pow,one_pow]; gcongr
    simpa only [one_mul,mul_one] using CSr 1 (w*cott h) x y U 1 hu (by norm_num) hz (by rw [h2]; norm_num)
  have hg:|cott h*x+w*y|≤V:=by
    have hz:(cott h)^2+w^2≤V^2:=by apply le_trans _ hf;gcongr
    simpa only [mul_one] using CSr (cott h) w x y V 1 hv (by norm_num) hz (by rw [h2]; norm_num)
  have heq:2*k*(PhiA h*u)=1+x+w*cott h*y:=by
    unfold PhiA; change 2*k*((u+w*cott h*v)/k*_)=_
    unfold x y; field_simp; nlinarith
  have heq':2*k*(PhiB h*v)=cott h-(cott h*x+w*y):=by
    unfold PhiB; change 2*k*((cott h*v-w*u)/k*_)=_
    unfold x y; field_simp
    linear_combination cott h*h1
  refine ⟨mul_le_mul_of_nonneg_left ?_ hs,mul_le_mul_of_nonneg_left ?_ hs,?_⟩
  · apply sub_le_sub_left
    rw [le_div_iff₀ (show 0<2*k by linarith)]
    change PhiA h*u*_≤_
    linarith [le_of_abs_le ht]
  · apply sub_le_sub_left
    rw [div_le_iff₀ (show 0<2*k by linarith)]
    change _≤ PhiA h*u*_
    linarith [(abs_le.mp ht).1]
  have hi: |PhiB h*v|≤(C+V)/(2*k):=by
    rw [le_div_iff₀ (show 0<2*k by linarith),mul_comm,
      show 2*k=|2*k| from (abs_of_nonneg (by linarith)).symm,← abs_mul]
    rw [heq']
    apply (abs_sub _ _).trans
    rw [abs_of_pos hp]; exact add_le_add hc hg
  have hv':|Real.tanh m|≤1:=by rw [← th_eq];nlinarith [(ri0 m).2,sq_abs (thR m)]
  rw [show Pdstar m h= -(s*(Real.tanh m*(PhiB h*v))) from by unfold Pdstar s v;ring,abs_neg,
    abs_mul,abs_of_nonneg hs,abs_mul]
  apply mul_le_mul_of_nonneg_left _ hs
  apply le_trans _ hi
  exact mul_le_of_le_one_left (abs_nonneg _) hv'

lemma fbase (_hh:0<h)(x:ℝ)(hx:0<x)(he:x ≤ sinh h):
    r^2/(1+w^2)*(w^2-1/x^2)≤fstar h:=by
  unfold fstar
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sub_le_sub_left
  apply div_le_div₀ zero_le_one _ (by positivity) (by gcongr)
  exact Real.sin_sq_le_one _

open Cert Cert.IV
lemma sh11:sinh (11/10:ℝ) ≥1335/1000 := by
  have hi:=mle (mbd 13350) (Row0.mHyp (mbd 11000)).1 (by decide +kernel)
  norm_num at *;exact hi
lemma arc11 (m:ℝ)(he:11/10 ≤ h):
    449/10000 ≤ fstar h ∧ 81/1000 ≤ Pastar h ∧
      Pastar h≤108/1000 ∧ |Pdstar m h|≤133/10000:=by
  have hh :0<h:=by linarith
  have ha:1335/1000 ≤ sinh h:= sh11.trans (sinh_le_sinh.mpr he)
  have hp:cott h≤125/100 := by
    unfold cott; rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.cosh_sq_sub_sinh_sq h,cosh_pos h]
  have hi:=arcBound m hh (125/100) (5837/1000) (4767/1000) hp
    (by norm_num) (by norm_num) (by norm_num [Profile.omegaP]) (by norm_num [Profile.omegaP])
  have hf:=fbase hh _ (by norm_num) ha
  dsimp only at *
  unfold Profile.r Profile.omegaP at *
  norm_num at *; refine ⟨?_,?_,?_,?_⟩ <;>linarith [hi.1,hi.2.1,hi.2.2]

lemma cb_mono {x:ℝ}(hx:0<x)(hh:x≤h): cott h≤cott x:=by
  unfold cott; rw [div_le_div_iff₀ (sinh_pos_iff.mpr (by linarith)) (sinh_pos_iff.mpr hx)]
  have hi:=sinh_nonneg_iff.mpr (show 0≤h-x by linarith);rw [sinh_sub] at hi; linarith
lemma arc30 (m:ℝ) (he:3/10 ≤h):
    2256/100000 ≤ fstar h ∧ Pastar h + |Pdstar m h| ≤150/1000 := by
  have hh:0<h:=by linarith
  have hp:304/1000 ≤ sinh h:= by
    apply le_trans _ (sinh_le_sinh.mpr he)
    have h:=sh3 (3/10) (by norm_num); norm_num at *; linarith
  have hc: cott h≤344/100:=by
    apply le_trans (cb_mono (by norm_num) he)
    have hi:= coth_est (show (0:ℝ)<3/10 by norm_num)
    unfold cott; linarith [hi.2]
  have hi:=arcBound m hh _ (1586/100) (575/100) hc
    (by norm_num) (by norm_num) (by norm_num [Profile.omegaP]) (by norm_num [Profile.omegaP])
  have hf:= fbase hh _ (by norm_num) hp
  dsimp only at *
  unfold Profile.r Profile.omegaP at *
  norm_num at *;constructor<;> linarith [hi.2.1,hi.2.2]
end GeneralMahler.SCal.SE

end

end OAI
