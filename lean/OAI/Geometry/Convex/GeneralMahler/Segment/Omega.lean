import OAI.Geometry.Convex.GeneralMahler.Segment.Element
import OAI.Geometry.Convex.GeneralMahler.Segment.Chord

namespace OAI
/-! Chord kernel bounds sharp enough for all midpoints. -/
noncomputable section
open Set Filter Real MeasureTheory
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Jet
variable (m:ℝ){h:ℝ}
lemma sh0 (hh:0<h):0 < shv h:= div_pos (Real.sinh_pos_iff.mpr hh) hh

def pm (m h t:ℝ):=(sinh t-sinh (m-h))/(2*cosh m*sinh h)
lemma θpm (_hh:0<h) (x:ℝ):
    cθ m h x=pm m h (loc m h x):=by
  unfold cθ seg pm leng seg xs left right; dsimp only
  rw [← hsinh m h, ← mul_sub, ← mul_sub]; field_simp [hsb.ne']
lemma negpm (hh:0<h)(t:ℝ):
    1-pm m h t=(sinh (m+h)-sinh t)/(2*cosh m*sinh h):=by
  have hi:=cosh_pos m
  have hp:=sinh_pos_iff.mpr hh
  unfold pm; field_simp; linarith [hsinh m h]

lemma pm_square (hh:0<h) (t:ℝ):
    (pm m h t*(1-pm m h t))*cosh m/cosh t ≤ 1/4:= by
  let a:=cosh m; let b:=cosh h; let c:=cosh t
  let r:=sinh m; let s:=sinh h; let v:=sinh t
  have hb:b≥1:=one_le_cosh _
  have ha:a≥1:=one_le_cosh _
  have hc:c≥1:=one_le_cosh _
  have he:=Real.cosh_sq_sub_sinh_sq h
  change b^2-s^2=1 at he
  have h1: a^2-r^2=1:=Real.cosh_sq_sub_sinh_sq m
  have hl : a*c-r*v≥1:= by
    unfold a c r v; rw [← Real.cosh_sub]
    apply Real.one_le_cosh
  have hp := nonneg_add_diag b a c r v hb ha hc hl h1
  have hT : a*(a-c)*s^2≤(v-r*b)^2 := by rw [show s^2=b^2-1 by linarith]; linarith
  have hf:s>0:= sinh_pos_iff.mpr hh
  rw [negpm m hh,pm,sinh_sub,sinh_add]
  change ((v-(r*b-a*s))/(2*a*s)*(((r*b+a*s)-v)/(2*a*s)))*a/c ≤ _
  field_simp
  nlinarith
where
  nonneg_add_diag (b a c r v:ℝ)(hb:b≥1)(ha:a≥1)(hc:c≥1)(hl:a*c-r*v≥1)
      (h1:a^2-r^2=1): 0 ≤ (v-r*b)^2-a*(a-c)*(b^2-1):=by
    have hi : (v-r*b)^2-a*(a-c)*(b^2-1)=(v-r)^2+2*(a*c-r*v-1)*(b-1)+(a*c-1)*(b-1)^2:= by
      linear_combination (1-b^2)*h1
    rw [hi]
    have h₁:0≤b-1:=sub_nonneg.mpr hb
    have h₂:0 ≤ a*c-r*v-1:=sub_nonneg.mpr hl
    have h₃:0 ≤ a*c-1:=by nlinarith
    positivity
lemma Wmax (hh:0<h)(x:ℝ): omega m h x ≤ (3/2)* shv h := by
  let t:=loc m h x
  have hi:= pm_square m hh t
  have hp:= sh0 hh
  unfold omega; rw [θpm m hh]
  apply le_trans _ (show 6*((pm m h t*(1-pm m h t))*cosh m/cosh t)*shv h≤(3/2:ℝ)*_ from by
    nlinarith)
  unfold t de; apply le_of_eq; ring

lemma sh_line (hh:0<h) (x:ℝ)(hx:x∈Icc (0:ℝ) 1): sinh (x*h) ≤ x*sinh h:=by
  have hf : ConvexOn ℝ (Ici 0) Real.sinh:=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0) Real.continuous_sinh.continuousOn
      (fun y _=>(Real.hasDerivAt_sinh y).hasDerivWithinAt) (fun y _=>(Real.hasDerivAt_cosh y).hasDerivWithinAt)
      (fun y hy=> Real.sinh_nonneg_iff.mpr (interior_subset hy))
  simpa only [smul_eq_mul,mul_zero,Real.sinh_zero,zero_add] using hf.2
    (mem_Ici.mpr (le_refl 0)) hh.le (sub_nonneg.mpr hx.2) hx.1 (sub_add_cancel 1 x)

lemma cfac (x y:ℝ) : 2*cosh x*cosh y=cosh (x+y)+cosh (x-y):=by rw [cosh_add,cosh_sub];ring
lemma sfac (x y:ℝ) : sinh x-sinh y=2*cosh ((x+y)/2)*sinh ((x-y)/2):=by
  let a:=(x+y)/2; let b:=(x-y)/2
  conv_lhs=> rw [show x=a+b from by unfold a b;ring,show y=a-b from by unfold a b;ring,sinh_add,sinh_sub]
  change _=2*cosh a*sinh b;ring
lemma pm_vsq (hh:0<h)(x:ℝ)(hx:x∈Icc (-1:ℝ) 1):
    let t:=m+h*x
    (pm m h t*(1-pm m h t))*cosh m/cosh t≤
      (1-x^2)*(1+cosh h)/8 := by
  intro t
  let a:=(1+x)/2;let b:=(1-x)/2
  let c:= (t+(m-h))/2;let d:=(m+h+t)/2
  have ha:a∈Icc (0:ℝ) 1:= by unfold a; constructor <;>linarith [hx.1,hx.2]
  have hb:b∈Icc (0:ℝ) 1:=by unfold b; constructor <;>linarith [hx.1,hx.2]
  have H : cosh c*cosh d/(cosh m*cosh t)≤ (1+cosh h)/2 := by
    have h₁:= cfac c d;have h₂:=cfac m t
    rw [show c+d=m+t by unfold c d;ring,show c-d=-h by unfold c d;ring,cosh_neg] at h₁
    let u:=cosh (m+t); let v:=cosh (m-t)
    have hu:1 ≤ u:=one_le_cosh _
    have hv:1 ≤ v:=one_le_cosh _
    have hr:1 ≤ cosh h:=one_le_cosh _
    rw [div_le_iff₀ (by positivity)]
    change 2*cosh c*cosh d= u+_ at h₁
    have hz:cosh m*cosh t=(u+v)/2:=by unfold u v; linarith
    rw [hz]; nlinarith
  have h₁: sinh t-sinh (m-h)=2*cosh c*sinh (a*h):=by
    rw [sfac,show (t-(m-h))/2=a*h from by unfold t a;ring]
  have h₂: sinh (m+h)-sinh t=2*cosh d*sinh (b*h):= by
    rw [sfac,show (m+h-t)/2=b*h from by unfold t b;ring]
  have hs:=sinh_pos_iff.mpr hh
  rw [negpm m hh,pm,h₁,h₂]
  have he : sinh (a*h)/sinh h≤a:=(div_le_iff₀ hs).mpr (sh_line hh a ha)
  have hh' : sinh (b*h)/sinh h≤b:=(div_le_iff₀ hs).mpr (sh_line hh b hb)
  let p:=(cosh c*cosh d/(cosh m*cosh t))
  have hpos : 0≤ sinh (b*h):=Real.sinh_nonneg_iff.mpr (mul_nonneg hb.1 hh.le)
  apply le_trans _ ((mul_le_mul_of_nonneg_left (mul_le_mul he hh' (div_nonneg hpos hs.le) ha.1)
    (show 0≤ p by unfold p; positivity)).trans ?_)
  · apply le_of_eq; unfold p;field_simp
  apply le_trans (mul_le_mul_of_nonneg_right H (mul_nonneg ha.1 hb.1))
  apply le_of_eq; unfold a b; ring

lemma Wpar (hh:0<h)(x:ℝ)(hx:x∈Icc (-1:ℝ) 1):
    omega m h x ≤ (3/4)*shv h*(1+cosh h)*(1-x^2):= by
  have he:=pm_vsq m hh x hx
  unfold omega; rw [θpm m hh]
  have ht:=mul_le_mul_of_nonneg_left he (show 0≤6*shv h by linarith [sh0 hh])
  unfold loc de loc; dsimp only at *; convert ht using 1 <;> first|rfl|ring
end GeneralMahler.SCal.SE

end

end OAI
