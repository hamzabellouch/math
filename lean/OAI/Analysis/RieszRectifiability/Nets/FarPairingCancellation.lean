import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.FarHeightTail

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem far_scalar_pairing_mean_zero_identity {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) (φ w : Ambient d → ℝ)
    (hφ : Integrable φ ν) (hφw : Integrable (fun x => φ x * w x) ν)
    (hzero : (∫ x, φ x ∂ν) = 0) (a y : Ambient d) (R : ℝ) (hR : 0 < R)
    (hnear : ∀ᵐ x ∂ν, 2 * dist x a ≤ R) (hfar : R ≤ dist a y) :
    Integrable (fun x => φ x * (w x - w y) * inverseDistancePow (m + 1) x y) ν ∧
      Integrable (fun x => φ x * (w x * inverseDistancePow (m + 1) x y -
        w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y))) ν ∧
      (∫ x, φ x * (w x - w y) * inverseDistancePow (m + 1) x y ∂ν) =
      ∫ x, φ x * (w x * inverseDistancePow (m + 1) x y -
        w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y)) ∂ν := by
  have hpos : 0 < dist a y := lt_of_lt_of_le hR hfar
  have hkmeas : Measurable (fun x => inverseDistancePow (m + 1) x y) := by
    unfold inverseDistancePow
    fun_prop
  have hkbound : ∀ᵐ x ∂ν, ‖inverseDistancePow (m + 1) x y‖ ≤ ((dist a y / 2) ^ (m + 1))⁻¹ := by
    filter_upwards [hnear] with x hx
    have hhalf : dist a y / 2 ≤ dist x y := by
      have ht := dist_triangle a x y
      rw [dist_comm a x] at ht
      linarith
    rw [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
    simpa only [inverseDistancePow, one_div] using!
      one_div_le_one_div_of_le (pow_pos (by positivity : 0 < dist a y / 2) (m + 1))
        (pow_le_pow_left₀ (by positivity) hhalf (m + 1))
  have hi : Integrable (fun x => φ x * (w x - w y) * inverseDistancePow (m + 1) x y) ν := by
    have h := (hφw.sub (hφ.mul_const (w y))).mul_bdd hkmeas.aestronglyMeasurable hkbound
    simpa only [mul_sub] using! h
  have hconst := hφ.mul_const (w y * inverseDistancePow (m + 1) a y)
  have heq : (fun x => φ x * (w x * inverseDistancePow (m + 1) x y -
      w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y))) =
      fun x => φ x * (w x - w y) * inverseDistancePow (m + 1) x y +
        φ x * (w y * inverseDistancePow (m + 1) a y) := by
    funext x
    ring
  refine ⟨hi, ?_, ?_⟩
  · rw [heq]
    exact hi.add hconst
  · rw [heq, integral_add hi hconst, integral_mul_const, hzero, zero_mul, add_zero]

end

end RieszRectifiability

end OAI
