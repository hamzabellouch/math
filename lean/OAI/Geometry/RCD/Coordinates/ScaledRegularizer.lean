import OAI.Geometry.RCD.Heat.HeatGramRebase

namespace OAI

/-! # A regularizer threshold fixed before the physical radius -/

open Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A bound on `|lambda| R^2`, rather than on `lambda`, is enough to
choose the scale threshold before the radius or regularizer is chosen. -/
theorem exists_scaled_regularizer_threshold {B Lambda η : ℝ}
    (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (R lambda : ℝ), |lambda| * R ^ 2 ≤ Lambda →
      ∀ k, N ≤ k → ∀ r, 0 ≤ r → (2 : ℝ) ^ k * r ≤ R →
      ∀ T : E →L[ℝ] E, ‖T‖ ^ 2 ≤ B →
        |lambda * r ^ 2| * ‖T‖ ^ 2 * (2 : ℝ) ^ k < η := by
  have hdecay : Tendsto (fun k : ℕ => (Lambda * B) * (1 / 2 : ℝ) ^ k)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (Lambda * B)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdecay.eventually_lt_const hη)
  refine ⟨N, ?_⟩
  intro R lambda hlambda k hk r hr hroot T hT
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hT (abs_nonneg (lambda * r ^ 2)))
    (by positivity : 0 ≤ (2 : ℝ) ^ k)
  have h2 := mul_le_mul_of_nonneg_right (dyadic_regularizer_le_geometric
    (lambda := lambda) hr k hroot) hB
  have h3 := mul_le_mul_of_nonneg_right hlambda (mul_nonneg hB
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k))
  have h4 : |lambda * r ^ 2| * B * (2 : ℝ) ^ k ≤
      (Lambda * B) * (1 / 2 : ℝ) ^ k := by
    nlinarith only [h2, h3]
  exact (h1.trans h4).trans_lt (hN k hk)

end RegularPointCoordinates

end

end OAI
