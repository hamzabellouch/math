import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # A first-order Taylor bound from the norm of the second derivative -/

open Set
namespace DefocusingNLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normedCurve_firstOrder_bound (u v w : ℝ → E) (r B : ℝ)
    (hB : 0 ≤ B)
    (hu : ∀ t ∈ Icc (-r) r, HasDerivAt u (v t) t)
    (hv : ∀ t ∈ Icc (-r) r, HasDerivAt v (w t) t)
    (hw : ∀ t ∈ Icc (-r) r, ‖w t‖ ≤ B)
    (t : ℝ) (ht : |t| ≤ r) :
    ‖u t - u 0 - t • v 0‖ ≤ B * |t| ^ 2 := by
  let s := Icc (-|t|) |t|
  have hsub : s ⊆ Icc (-r) r := by
    intro x hx
    exact ⟨(neg_le_neg ht).trans hx.1, hx.2.trans ht⟩
  have h0 : (0 : ℝ) ∈ s := ⟨neg_nonpos.mpr (abs_nonneg _), abs_nonneg _⟩
  have htt : t ∈ s := ⟨neg_abs_le t, le_abs_self t⟩
  have hdb (x : ℝ) (hx : x ∈ s) : ‖v x - v 0‖ ≤ B * |t| := by
    have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hv y (hsub hy)).hasDerivWithinAt)
      (fun y hy => hw y (hsub hy)) (convex_Icc (-|t|) |t|) h0 hx
    simp only [sub_zero, Real.norm_eq_abs] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hx) hB)
  let f := fun x => u x - u 0 - x • v 0
  have hd (x : ℝ) (hx : x ∈ s) : HasDerivWithinAt f (v x - v 0) s x := by
    have hh := ((hu x (hsub hx)).sub_const (u 0)).sub
      ((hasDerivAt_id x).smul_const (v 0))
    convert hh.hasDerivWithinAt using 1
    · rfl
    · simp only [one_smul]
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hdb (convex_Icc (-|t|) |t|) h0 htt
  simpa only [f, zero_smul, sub_self, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using hb

end DefocusingNLS

end OAI
