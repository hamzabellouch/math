import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ExteriorDilation
import OAI.Analysis.RieszRectifiability.Limits.ExteriorTailLimit
import OAI.Analysis.RieszRectifiability.Limits.PolynomialLeadingLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

theorem exterior_dilation_coefficient_le_one (d k : ℕ) (hk : 2 ≤ k)
    (r : ℝ) (hr : 1 ≤ r) : r ^ (d + 2) * (r ^ k)⁻¹ * (r ^ d)⁻¹ ≤ 1 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  calc
    _ = r ^ 2 * (r ^ k)⁻¹ := by
      rw [pow_add]
      have hz : r ^ d ≠ 0 := pow_ne_zero _ hrpos.ne'
      field_simp
    _ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one (pow_pos hrpos k)).2 (pow_le_pow_right₀ hr hk)

theorem normalized_exterior_weighted_integral_tendsto_zero {d : ℕ}
    (k : ℕ) (hk : 2 ≤ k) (f : Ambient d → ℂ)
    (hi : IntegrableOn (fun x => ‖f x‖ * inverseDistancePow (d + 2) 0 x)
      (closedExterior 0 1)) :
    Tendsto (fun j => ∫ x in closedExterior (0 : Ambient d) 1,
      ‖((polynomialExpansionRadius j : ℂ) ^ k)⁻¹ * f (polynomialExpansionRadius j • x)‖ *
        inverseDistancePow (d + 2) 0 x) atTop (𝓝 0) := by
  have htail := exterior_integral_tendsto_zero volume (0 : Ambient d)
    (fun x => ‖f x‖ * inverseDistancePow (d + 2) 0 x) hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
  · intro j
    exact integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (inverseDistancePow_nonneg _ _ _))
  · intro j
    dsimp only
    rw [exterior_weighted_normalized_dilation_integral (d + 2) k f
      (polynomialExpansionRadius j) (polynomialExpansionRadius_pos j)]
    have hr : 1 ≤ polynomialExpansionRadius j := by
      unfold polynomialExpansionRadius
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have hn : 0 ≤ ∫ x in closedExterior (0 : Ambient d) (polynomialExpansionRadius j),
        ‖f x‖ * inverseDistancePow (d + 2) 0 x :=
      integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (inverseDistancePow_nonneg _ _ _))
    simpa only [one_mul, polynomialExpansionRadius] using!
      mul_le_mul_of_nonneg_right (exterior_dilation_coefficient_le_one d k hk _ hr) hn

end

end RieszRectifiability

end OAI
