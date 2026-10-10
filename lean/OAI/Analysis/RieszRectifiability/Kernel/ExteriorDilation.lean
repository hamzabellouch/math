import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ClosedTailBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped Pointwise

theorem smul_closedExterior_unit {d : ℕ} (r : ℝ) (hr : 0 < r) :
    r • closedExterior (0 : Ambient d) 1 = closedExterior 0 r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change r ≤ dist (0 : Ambient d) (r • y)
    change 1 ≤ dist (0 : Ambient d) y at hy
    simp only [dist_zero_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at *
    nlinarith
  · intro hx
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · change 1 ≤ dist (0 : Ambient d) (r⁻¹ • x)
      change r ≤ dist (0 : Ambient d) x at hx
      rw [dist_zero_left, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      rw [dist_zero_left] at hx
      exact (le_inv_mul_iff₀ hr).2 (by simpa using! hx)
    · change r • (r⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

theorem inverseDistancePow_origin_smul {d : ℕ} (q : ℕ)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    inverseDistancePow q 0 (r • x) = (r ^ q)⁻¹ * inverseDistancePow q 0 x := by
  simp only [inverseDistancePow, dist_zero_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, mul_pow, mul_inv]

theorem exterior_weighted_normalized_dilation_integral {d : ℕ} (q k : ℕ)
    (f : Ambient d → ℂ) (r : ℝ) (hr : 0 < r) :
    (∫ x in closedExterior (0 : Ambient d) 1,
      ‖((r : ℂ) ^ k)⁻¹ * f (r • x)‖ * inverseDistancePow q 0 x) =
      (r ^ q * (r ^ k)⁻¹ * (r ^ d)⁻¹) *
        ∫ x in closedExterior (0 : Ambient d) r, ‖f x‖ * inverseDistancePow q 0 x := by
  have hpoint (x : Ambient d) :
      ‖((r : ℂ) ^ k)⁻¹ * f (r • x)‖ * inverseDistancePow q 0 x =
      (r ^ q * (r ^ k)⁻¹) * (‖f (r • x)‖ * inverseDistancePow q 0 (r • x)) := by
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      inverseDistancePow_origin_smul q r hr]
    have hz : r ^ q ≠ 0 := pow_ne_zero _ hr.ne'
    field_simp
  calc
    _ = ∫ x in closedExterior (0 : Ambient d) 1,
        (r ^ q * (r ^ k)⁻¹) * (‖f (r • x)‖ * inverseDistancePow q 0 (r • x)) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (r ^ q * (r ^ k)⁻¹) * ∫ x in closedExterior (0 : Ambient d) 1,
        (‖f (r • x)‖ * inverseDistancePow q 0 (r • x)) := integral_const_mul _ _
    _ = _ := by
      rw [Measure.setIntegral_comp_smul volume (fun x => ‖f x‖ * inverseDistancePow q 0 x)
        (closedExterior (0 : Ambient d) 1) hr.ne', smul_closedExterior_unit r hr,
        finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hr d)), smul_eq_mul]
      ring

end

end RieszRectifiability

end OAI
