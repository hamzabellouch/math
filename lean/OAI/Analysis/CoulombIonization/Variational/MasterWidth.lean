import Mathlib
import OAI.Analysis.CoulombIonization.Model

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Metric
open scoped NNReal

def masterExponent : ℝ := 1/100000

def masterBaseDistance (r₀ : ℝ) (x : Space) : ℝ := max ‖x‖ r₀

def masterWidth (c₁ r₀ s : ℝ) (x : Space) : ℝ :=
  c₁*masterBaseDistance r₀ x*(min (masterBaseDistance r₀ x) s)^masterExponent

lemma masterExponent_pos : 0 < masterExponent := by norm_num [masterExponent]
lemma masterExponent_nonneg : 0 ≤ masterExponent := masterExponent_pos.le

lemma powerProfile_interval {w s x y : ℝ} (hw : 0 ≤ w) (hx : 0 < x)
    (hxy : x ≤ y) (hys : y ≤ s) :
    ‖y^(1+w)-x^(1+w)‖ ≤ (1+w)*s^w*(y-x) := by
  have hp : 0 ≤ 1+w := by linarith
  have hd (z : ℝ) (hz : z ∈ Icc x y) :
      HasDerivWithinAt (fun u : ℝ => u^(1+w)) ((1+w)*z^w) (Icc x y) z := by
    have hh := (Real.hasDerivAt_rpow_const (x := z) (p := 1+w)
      (Or.inl (ne_of_gt (hx.trans_le hz.1)))).hasDerivWithinAt (s := Icc x y)
    simpa only [add_sub_cancel_left] using hh
  have hb (z : ℝ) (hz : z ∈ Icc x y) : ‖(1+w)*z^w‖ ≤ (1+w)*s^w := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp (Real.rpow_nonneg (hx.le.trans hz.1) _))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hx.le.trans hz.1) (hz.2.trans hys) hw) hp
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc x y)
    (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxy)] using H

def cappedWidthProfile (s w d : ℝ) : ℝ := d*(min d s)^w

lemma cappedWidthProfile_small {s w d : ℝ} (hd : 0 < d) (hw : 0 ≤ w) (hs : d ≤ s) :
    cappedWidthProfile s w d = d^(1+w) := by
  rw [cappedWidthProfile,min_eq_left hs,Real.rpow_one_add' hd.le (by linarith)]

lemma cappedWidthProfile_large {s w d : ℝ} (hs : s ≤ d) :
    cappedWidthProfile s w d = d*s^w := by rw [cappedWidthProfile,min_eq_right hs]

lemma cappedWidthProfile_ordered_bound {w s x y : ℝ} (hw : 0 ≤ w) (hs : 0 < s)
    (hx : 0 < x) (hxy : x ≤ y) :
    ‖cappedWidthProfile s w y-cappedWidthProfile s w x‖ ≤ (1+w)*s^w*(y-x) := by
  have hy : 0 < y := hx.trans_le hxy
  by_cases hys : y ≤ s
  · rw [cappedWidthProfile_small hy hw hys,cappedWidthProfile_small hx hw (hxy.trans hys)]
    exact powerProfile_interval hw hx hxy hys
  have hsy : s ≤ y := le_of_not_ge hys
  by_cases hsx : s ≤ x
  · rw [cappedWidthProfile_large hsy,cappedWidthProfile_large hsx,←sub_mul,
      norm_mul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxy),
      Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hs.le _)]
    nlinarith [mul_nonneg hw (mul_nonneg (Real.rpow_nonneg hs.le w) (sub_nonneg.mpr hxy))]
  have hxs : x ≤ s := le_of_not_ge hsx
  have hsmall : ‖cappedWidthProfile s w s-cappedWidthProfile s w x‖ ≤
      (1+w)*s^w*(s-x) := by
    rw [cappedWidthProfile_small hs hw le_rfl,cappedWidthProfile_small hx hw hxs]
    exact powerProfile_interval hw hx hxs le_rfl
  have hlarge : ‖cappedWidthProfile s w y-cappedWidthProfile s w s‖ ≤
      (1+w)*s^w*(y-s) := by
    rw [cappedWidthProfile_large hsy,cappedWidthProfile_large le_rfl,←sub_mul,
      norm_mul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hsy),
      Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hs.le _)]
    nlinarith [mul_nonneg hw (mul_nonneg (Real.rpow_nonneg hs.le w) (sub_nonneg.mpr hsy))]
  calc
    _ = ‖(cappedWidthProfile s w y-cappedWidthProfile s w s)+
        (cappedWidthProfile s w s-cappedWidthProfile s w x)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ (1+w)*s^w*(y-s)+(1+w)*s^w*(s-x) := add_le_add hlarge hsmall
    _ = _ := by ring

lemma cappedWidthProfile_norm_bound {w s x y : ℝ} (hw : 0 ≤ w) (hs : 0 < s)
    (hx : 0 < x) (hy : 0 < y) :
    ‖cappedWidthProfile s w x-cappedWidthProfile s w y‖ ≤ (1+w)*s^w*‖x-y‖ := by
  rcases le_total y x with h|h
  · simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr h)] using
      cappedWidthProfile_ordered_bound hw hs hy h
  · simpa only [norm_sub_rev x y,norm_sub_rev (cappedWidthProfile s w x) _,
      Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr h)] using
      cappedWidthProfile_ordered_bound hw hs hx h

lemma masterBaseDistance_lipschitz (r₀ : ℝ) : LipschitzWith 1 (masterBaseDistance r₀) :=
  lipschitzWith_one_norm.max_const r₀

lemma masterWidth_pos {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (x : Space) : 0 < masterWidth c₁ r₀ s x := by
  have hD : 0 < masterBaseDistance r₀ x := hr.trans_le (le_max_right _ _)
  exact mul_pos (mul_pos hc hD) (Real.rpow_pos_of_pos (lt_min hD hs) _)

lemma masterWidth_upper {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hs : 0 < s)
    (x : Space) : masterWidth c₁ r₀ s x ≤ c₁*masterBaseDistance r₀ x*s^masterExponent := by
  have hD : 0 < masterBaseDistance r₀ x := hr.trans_le (le_max_right _ _)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_min hD.le hs.le) (min_le_right _ _) masterExponent_nonneg)
    (mul_nonneg hc hD.le)

lemma masterWidth_lower {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hrs : r₀ ≤ s)
    (x : Space) : c₁*r₀^(1+masterExponent) ≤ masterWidth c₁ r₀ s x := by
  have hD : r₀ ≤ masterBaseDistance r₀ x := le_max_right _ _
  rw [Real.rpow_one_add' hr.le (by linarith [masterExponent_pos])]
  simpa only [masterWidth,mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hD (Real.rpow_le_rpow hr.le (le_min hD hrs) masterExponent_nonneg)
      (Real.rpow_nonneg hr.le _) (hr.le.trans hD)) hc

lemma masterWidth_lipschitz {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hs : 0 < s) :
    LipschitzWith ⟨c₁*(1+masterExponent)*s^masterExponent, by
      exact mul_nonneg (mul_nonneg hc (by linarith [masterExponent_pos])) (Real.rpow_nonneg hs.le _)⟩
      (masterWidth c₁ r₀ s) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : 0 < masterBaseDistance r₀ x := hr.trans_le (le_max_right _ _)
  have hy : 0 < masterBaseDistance r₀ y := hr.trans_le (le_max_right _ _)
  have H := cappedWidthProfile_norm_bound masterExponent_nonneg hs hx hy
  have hd := (masterBaseDistance_lipschitz r₀).dist_le_mul x y
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,←Real.norm_eq_abs] at hd
  change dist (masterWidth c₁ r₀ s x) (masterWidth c₁ r₀ s y) ≤
    (c₁*(1+masterExponent)*s^masterExponent)*dist x y
  simp only [dist_eq_norm,masterWidth]
  have he : c₁*masterBaseDistance r₀ x*(min (masterBaseDistance r₀ x) s)^masterExponent-
      c₁*masterBaseDistance r₀ y*(min (masterBaseDistance r₀ y) s)^masterExponent =
      c₁*(cappedWidthProfile s masterExponent (masterBaseDistance r₀ x)-
        cappedWidthProfile s masterExponent (masterBaseDistance r₀ y)) := by
    simp only [cappedWidthProfile]; ring
  rw [he,norm_mul,Real.norm_eq_abs,abs_of_nonneg hc]
  have hp : 0 ≤ (1+masterExponent)*s^masterExponent :=
    mul_nonneg (by linarith [masterExponent_pos]) (Real.rpow_nonneg hs.le _)
  calc
    _ ≤ c₁*((1+masterExponent)*s^masterExponent*‖masterBaseDistance r₀ x-masterBaseDistance r₀ y‖) :=
      mul_le_mul_of_nonneg_left H hc
    _ ≤ c₁*((1+masterExponent)*s^masterExponent*dist x y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hp) hc
    _ = _ := by rw [dist_eq_norm]; ring

open Set Metric
open scoped NNReal

def widthKernel (t : Space → ℝ) (h : Space → ℝ) (x y : Space) : ℝ :=
  (t x)⁻¹^3*h ((t x)⁻¹ • (y-x))

lemma invCube_norm_sub_le {q a b : ℝ} (hq : 0 < q) (ha : q ≤ a) (hb : q ≤ b) :
    ‖a⁻¹^3-b⁻¹^3‖ ≤ 3*q⁻¹^4*‖a-b‖ := by
  have hd (z : ℝ) (hz : z ∈ Ici q) :
      HasDerivWithinAt (fun u : ℝ => u⁻¹^3) (-3*z⁻¹^4) (Ici q) z := by
    have hh := ((hasDerivAt_inv (ne_of_gt (hq.trans_le hz))).pow 3).hasDerivWithinAt (s := Ici q)
    convert! hh using 1; simp only [Nat.cast_ofNat, Nat.reduceSub, ←inv_pow]
    ring
  have hbound (z : ℝ) (hz : z ∈ Ici q) : ‖-3*z⁻¹^4‖ ≤ 3*q⁻¹^4 := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_neg (by norm_num : (-3:ℝ) < 0)]
    norm_num only [neg_neg,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hq.le.trans hz)) 4)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr (hq.le.trans hz))
      (inv_anti₀ hq hz) 4) (by norm_num)
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound (convex_Ici q) hb ha

lemma normalizedArgument_distance {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) {q : ℝ} (hq : 0 < q) (hl : ∀ x, q ≤ t x)
    (x z y : Space) (ha : ‖(t x)⁻¹ • (y-x)‖ ≤ 1) :
    ‖(t x)⁻¹ • (y-x)-(t z)⁻¹ • (y-z)‖ ≤ q⁻¹*(1+(T:ℝ))*‖x-z‖ := by
  let a := (t x)⁻¹ • (y-x)
  have hx : 0 < t x := hq.trans_le (hl x)
  have hz : 0 < t z := hq.trans_le (hl z)
  have hax : t x • a = y-x := by simp [a,smul_smul,hx.ne']
  have he : a-(t z)⁻¹ • (y-z) = (t z)⁻¹ • ((t z-t x) • a+(z-x)) := by
    apply (smul_right_injective Space hz.ne')
    simp only [smul_sub,smul_smul,mul_inv_cancel₀ hz.ne',one_smul,sub_smul,hax]
    abel
  change ‖a-(t z)⁻¹ • (y-z)‖ ≤ _
  rw [he,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hz.le)]
  have hh := ht.dist_le_mul z x
  simp only [dist_eq_norm,norm_sub_rev z x] at hh
  have hn : ‖(t z-t x) • a+(z-x)‖ ≤ (1+(T:ℝ))*‖x-z‖ := by
    calc
      _ ≤ ‖(t z-t x) • a‖+‖z-x‖ := norm_add_le _ _
      _ = ‖t z-t x‖*‖a‖+‖x-z‖ := by rw [norm_smul,norm_sub_rev z x]
      _ ≤ ‖t z-t x‖*1+‖x-z‖ := add_le_add_left (mul_le_mul_of_nonneg_left ha (norm_nonneg _)) _
      _ ≤ ((T:ℝ)*‖x-z‖)*1+‖x-z‖ := by nlinarith only [hh]
      _ = _ := by ring
  calc
    _ ≤ (t z)⁻¹*((1+(T:ℝ))*‖x-z‖) := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hz.le)
    _ ≤ q⁻¹*((1+(T:ℝ))*‖x-z‖) := mul_le_mul_of_nonneg_right (inv_anti₀ hq (hl z)) (by positivity)
    _ = _ := by ring

lemma widthKernel_active_norm_bound {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) {q : ℝ} (hq : 0 < q) (hl : ∀ x, q ≤ t x)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (_hM : 0 ≤ M)
    (hb : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1)
    (x z y : Space) (hx : h ((t x)⁻¹ • (y-x)) ≠ 0) :
    ‖widthKernel t h x y-widthKernel t h z y‖ ≤
      ((3*M*(T:ℝ)+(H:ℝ)*(1+(T:ℝ)))*q⁻¹^4)*‖x-z‖ := by
  have hq0 := inv_nonneg.mpr hq.le
  have htpos (u : Space) : 0 < t u := hq.trans_le (hl u)
  have ha : ‖(t x)⁻¹ • (y-x)‖ ≤ 1 := by
    simpa only [mem_closedBall,dist_zero_right] using hs hx
  have hc := invCube_norm_sub_le hq (hl x) (hl z)
  have hwd := ht.dist_le_mul x z
  simp only [dist_eq_norm] at hwd
  have hc' : ‖(t x)⁻¹^3-(t z)⁻¹^3‖ ≤ 3*q⁻¹^4*((T:ℝ)*‖x-z‖) :=
    hc.trans (mul_le_mul_of_nonneg_left hwd (by positivity))
  have ha' := normalizedArgument_distance ht hq hl x z y ha
  have hhd := hh.dist_le_mul ((t x)⁻¹ • (y-x)) ((t z)⁻¹ • (y-z))
  simp only [dist_eq_norm] at hhd
  have hh' := hhd.trans (mul_le_mul_of_nonneg_left ha' H.coe_nonneg)
  have hi : ‖(t z)⁻¹^3‖ ≤ q⁻¹^3 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (htpos z).le) _)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (htpos z).le) (inv_anti₀ hq (hl z)) 3
  have he : widthKernel t h x y-widthKernel t h z y =
      ((t x)⁻¹^3-(t z)⁻¹^3)*h ((t x)⁻¹ • (y-x))+
      (t z)⁻¹^3*(h ((t x)⁻¹ • (y-x))-h ((t z)⁻¹ • (y-z))) := by
    simp only [widthKernel]; ring
  rw [he]
  calc
    _ ≤ ‖((t x)⁻¹^3-(t z)⁻¹^3)*h ((t x)⁻¹ • (y-x))‖+
        ‖(t z)⁻¹^3*(h ((t x)⁻¹ • (y-x))-h ((t z)⁻¹ • (y-z)))‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul,norm_mul]
    _ ≤ (3*q⁻¹^4*((T:ℝ)*‖x-z‖))*M+
        q⁻¹^3*((H:ℝ)*(q⁻¹*(1+(T:ℝ))*‖x-z‖)) :=
      add_le_add (mul_le_mul hc' (hb _) (norm_nonneg _) (by positivity))
        (mul_le_mul hi hh' (norm_nonneg _) (by positivity))
    _ = _ := by ring

lemma widthKernel_lipschitz {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) {q : ℝ} (hq : 0 < q) (hl : ∀ x, q ≤ t x)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    LipschitzWith ⟨(3*M*(T:ℝ)+(H:ℝ)*(1+(T:ℝ)))*q⁻¹^4, by positivity⟩
      (fun x => widthKernel t h x y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  change dist (widthKernel t h x y) (widthKernel t h z y) ≤
    ((3*M*(T:ℝ)+(H:ℝ)*(1+(T:ℝ)))*q⁻¹^4)*dist x z
  simp only [dist_eq_norm]
  by_cases hx : h ((t x)⁻¹ • (y-x)) ≠ 0
  · exact widthKernel_active_norm_bound ht hq hl hh hM hb hs x z y hx
  by_cases hz : h ((t z)⁻¹ • (y-z)) ≠ 0
  · simpa only [norm_sub_rev z x,norm_sub_rev (widthKernel t h z y) _] using
      widthKernel_active_norm_bound ht hq hl hh hM hb hs z x y hz
  simp only [not_ne_iff] at hx hz
  simp only [widthKernel,hx,hz,mul_zero,sub_zero,norm_zero]
  positivity

end CoulombAtom

end

end OAI
