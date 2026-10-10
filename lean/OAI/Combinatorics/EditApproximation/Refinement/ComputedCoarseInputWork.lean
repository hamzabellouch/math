import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseInputWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedExecutionCosts

namespace OAI

namespace EditApproximation
open Filter MeasureTheory

noncomputable def computedFamilyCoarseInputWork (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) : ℝ :=
  physicalFamilyCoarseInputWork source target N (integerParameters N).P (inputHeight N)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    (clampedSeedNat input.1) input.2 (16384 * inputHeight N + 5)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (computedFinalRoot source target N)

theorem computedFamilyCoarseInputWork_le (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
    (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseInputWork source target N input ≤ computedWidthEnvelope N := by
  have hc := physicalFamilyCoarseInputWork_le source target N (integerParameters N).P (inputHeight N)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    (clampedSeedNat input.1) (computedParameterP_pos N) input.2 (16384 * inputHeight N + 5)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (computedFamilyMemoCode_injective source target N (inputHeight N ^ 2) hN
      (two_hundred_le_two_pow_thousand.trans hell))
    (computedFamilyMemoCode_fits source target N (inputHeight N ^ 2) hN hell hsize le_rfl hB)
    (computedFinalRoot source target N) rfl
  have hh : 105 ≤ inputHeight N :=
    (by omega : 105 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  exact hc.trans (computedFamilyTree_width_le source target N hN
    (two_hundred_le_two_pow_thousand.trans hell) hh hsize input)

theorem computedFamilyCoarseInputWork_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
        computedFamilyCoarseInputWork source target N input ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_weighted_near_linear 0 epsilon hepsilon,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    computed_localOnlineMassBound_word] with N hw hN hell hB
  intro source target hsize input
  exact (computedFamilyCoarseInputWork_le source target N (by omega) hell hsize hB input).trans (by simpa only [pow_zero, mul_one] using hw)

noncomputable def computedExecutionCoarseInputWork (source target : List ℕ) (N : ℕ)
    (execution : ComputedExecutionOutcome source target N) : ℝ :=
  computedFamilyCoarseInputWork source target N (computedExecutionAccepted source target N execution)

theorem computedExecutionCoarseInputWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionCoarseInputWork source target N) (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N (computedFamilyCoarseInputWork source target N)

theorem computedExecutionCoarseInputWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionCoarseInputWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedFamilyCoarseInputWork_near_linear epsilon hepsilon] with N hN
  intro source target hsize
  calc
    _ ≤ ∫ _ : ComputedExecutionOutcome source target N, (N + 2 : ℝ) ^ (1 + epsilon)
        ∂computedExecutionLaw source target N :=
      integral_mono (computedExecutionCoarseInputWork_integrable source target N) (integrable_const _)
        (fun execution => hN source target hsize _)
    _ = _ := by simp

end EditApproximation

end OAI
