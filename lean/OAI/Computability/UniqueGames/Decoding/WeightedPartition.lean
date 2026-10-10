import OAI.Computability.UniqueGames.Foundations.Conditioning
import OAI.Computability.UniqueGames.Foundations.ValueLemmas

namespace OAI

section

/-!
Weighted total probability for the public clean-coordinate observation.
The observation may have zero-probability fibres. Only its positive fibres
require a conditional bound; the identity itself is proved from finite sums.
-/

namespace UniqueGamesTheorem.Clean.WeightedPartition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {Ω H : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]

def fibre (observe : Ω → H) (h : H) : Ω → Bool :=
  fun x => decide (observe x = h)

theorem sum_fibre_inter (μ : FiniteDistribution Ω) (observe : Ω → H)
    (event : Ω → Bool) :
    (∑ h, μ.probability (fun x => fibre observe h x && event x)) =
      μ.probability event := by
  classical
  unfold FiniteDistribution.probability fibre
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : event x = true <;> simp [hx]

theorem sum_fibre_bound (μ : FiniteDistribution Ω) (observe : Ω → H)
    (bound : H → ℝ) :
    (∑ h, μ.probability (fibre observe h) * bound h) =
      μ.expectation (fun x => bound (observe x)) := by
  classical
  unfold FiniteDistribution.probability FiniteDistribution.expectation fibre
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq, ite_mul, zero_mul]
  simp

/-- The averaging step for a genuine weighted observation. No conditional
independence or law-of-total-probability equality is supplied as a premise. -/
theorem probability_le_conditional_bounds (μ : FiniteDistribution Ω)
    (observe : Ω → H) (event : Ω → Bool) (bound : H → ℝ)
    (conditional : ∀ h (positive : 0 < μ.probability (fibre observe h)),
      (μ.condition (fibre observe h) positive).probability event ≤ bound h) :
    μ.probability event ≤ μ.expectation (fun x => bound (observe x)) := by
  rw [← sum_fibre_inter μ observe event, ← sum_fibre_bound μ observe bound]
  apply Finset.sum_le_sum
  intro h _
  by_cases positive : 0 < μ.probability (fibre observe h)
  · rw [μ.probability_inter_eq_mul_conditional (fibre observe h) event positive]
    exact mul_le_mul_of_nonneg_left (conditional h positive) positive.le
  · have zero : μ.probability (fibre observe h) = 0 :=
      le_antisymm (le_of_not_gt positive) (μ.probability_nonnegative _)
    rw [μ.probability_and_eq_zero_of_probability_eq_zero (fibre observe h) event zero,
      zero, zero_mul]

/-- A constant bound survives arbitrary public outside observations. -/
theorem probability_le_of_conditional_le (μ : FiniteDistribution Ω)
    (observe : Ω → H) (event : Ω → Bool) (bound : ℝ)
    (conditional : ∀ h (positive : 0 < μ.probability (fibre observe h)),
      (μ.condition (fibre observe h) positive).probability event ≤ bound) :
    μ.probability event ≤ bound := by
  have estimate := probability_le_conditional_bounds μ observe event
    (fun _ => bound) conditional
  have constant : μ.expectation (fun _ => bound) = bound := by
    rw [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized, one_mul]
  simpa only [constant] using estimate

end
end UniqueGamesTheorem.Clean.WeightedPartition

end

end OAI
