import OAI.Geometry.RCD.Coordinates.BilinearHeatEnvelope
import OAI.Geometry.RCD.Sobolev.DyadicBochnerMass

namespace OAI

/-! # Summing the long-time source blocks in the same geometric envelope -/

open scoped BigOperators InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

/-- The displacement factor contributes one half per time block. Its
convolution with a three-quarter envelope loses only a factor three. -/
theorem half_convolution_le_three_quarters (F : ℕ → ℝ)
    (hF : ∀ i, 0 ≤ F i) (hstep : ∀ i, (3 / 4 : ℝ) * F i ≤ F (i + 1)) (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), (1 / 2 : ℝ) ^ (i - j) * F j) ≤ 3 * F i := by
  induction i with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one, Nat.sub_self, pow_zero, one_mul]
    linarith [hF 0]
  | succ i ih =>
    rw [geometric_causal_sum_succ]
    have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith [hstep i]

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [BorelSpace X] in
/-- Exact recurrence for the actual full-mass envelope. -/
theorem dyadicBochnerEnvelope_step (M : PositiveBilinearMeasure X E) (n : ℕ)
    (x : X) (R : ℝ) (i : ℕ) (v : E) :
    ⟪v, dyadicBochnerEnvelope M n x R (i + 1) v⟫_ℝ =
      (3 / 4 : ℝ) * ⟪v, dyadicBochnerEnvelope M n x R i v⟫_ℝ +
        ⟪v, dyadicBochnerMass M n x R (i + 1) v⟫_ℝ := by
  simp only [dyadicBochnerEnvelope_inner, geometric_causal_sum_succ, pow_succ]
  ring

/-- Summing all time blocks preserves the original full-mass envelope;
no enlarged mass or new source hypothesis is introduced. -/
theorem dyadicBochnerEnvelope_time_sum_le (M : PositiveBilinearMeasure X E) (n : ℕ)
    (x : X) {R : ℝ} (hR : 0 ≤ R) (i : ℕ) (v : E) :
    (∑ j ∈ Finset.range (i + 1), (1 / 2 : ℝ) ^ (i - j) *
      ⟪v, dyadicBochnerEnvelope M n x R j v⟫_ℝ) ≤
        3 * ⟪v, dyadicBochnerEnvelope M n x R i v⟫_ℝ := by
  apply half_convolution_le_three_quarters
  · exact fun j => (dyadicBochnerEnvelope_isPositive M n x hR j).inner_nonneg_right v
  · intro j
    rw [dyadicBochnerEnvelope_step]
    exact le_add_of_nonneg_right ((dyadicBochnerMass_isPositive M n x hR (j + 1)).inner_nonneg_right v)

end RegularPointCoordinates

end

end OAI
