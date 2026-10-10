import OAI.Combinatorics.BalancedRyser.Probability.BoundedDriftCore
import OAI.Combinatorics.BalancedRyser.Probability.CenteredIncrements
import OAI.Combinatorics.BalancedRyser.Probability.Concentration
import OAI.Combinatorics.BalancedRyser.Probability.SubGaussianTail

namespace OAI

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal

namespace Balanced
open scoped _root_.Balanced

universe u

theorem boundedDriftConcentration_proof : BoundedDriftConcentration.{u} := by
  intro Ω mΩ μ hμ ℱ X T L hT hL hX hbound u hu t ht
  let Y : ℕ → Ω → ℝ := fun j ω ↦ X (j + 1) ω - X j ω -
    μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω
  have hmeas (j : ℕ) (hj : j < t) : StronglyMeasurable[ℱ (j + 1)] (Y j) := by
    exact stronglyMeasurable_centered_increment_of_measurable j
      (hX j (by omega)) (hX (j + 1) (by omega))
  have hb (j : ℕ) (hj : j < t) : ∀ᵐ ω ∂μ, |Y j ω| ≤ 2 * L :=
    abs_sub_condExp_le (hbound j (by omega))
  have hz (j : ℕ) (hj : j < t) : μ[Y j | ℱ j] =ᵐ[μ] 0 := by
    apply condExp_sub_condExp_eq_zero (ℱ.le j)
    apply integrable_of_abs_le
      ((((hX (j + 1) (by omega)).mono (ℱ.le (j + 1))).sub
        ((hX j (by omega)).mono (ℱ.le j))).measurable.aemeasurable)
      (hbound j (by omega))
  have hmgf := subGaussian_sum_of_bounded_differences
    (μ := μ) (ℱ := ℱ) (Y := Y) (by positivity : 0 < 2 * L) t hmeas hb hz
  have hp : (((t : ℝ≥0) * ⟨(2 * L) ^ 2, sq_nonneg (2 * L)⟩ : ℝ≥0) : ℝ)
      ≤ 4 * (t : ℝ) * L ^ 2 := by
    change (t : ℝ) * (2 * L) ^ 2 ≤ 4 * (t : ℝ) * L ^ 2
    nlinarith
  have htail := subGaussian_abs_tail_horizon hmgf ht hp hu.le
  simpa only [Y, sum_centered_increments_eq] using htail

end Balanced

end OAI
