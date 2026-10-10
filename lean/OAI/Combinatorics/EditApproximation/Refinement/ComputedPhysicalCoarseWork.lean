import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseExecution
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseBudget
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

open MeasureTheory Filter




noncomputable def computedPhysicalCoarseWork (source target : List ℕ) (N : ℕ) :
    ComputedFamilyDraw source target N → ComputedPhysicalCoarseDraw source target N → ℝ := by
  intro draw
  with_reducible
    exact physicalFamilyMemoCoarseWork (M := (integerParameters N).M)
      (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
      source target N (integerParameters N).P (inputHeight N) (integerParameters N).T
      (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N)
      (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
      (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
      draw (integerParameters N).B (computedPhysicalCoarseDepth source target N)
      (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
      (computedFinalRoot source target N)


def ComputedPhysicalCoarseBudget (source target : List ℕ) (N : ℕ) (budget : ℝ) : Prop :=
  SymbolicComputedCoarseBudget (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
    (B := (integerParameters N).B) source target N (computedPhysicalCoarseDepth source target N)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2)) budget

 theorem computedPhysicalCoarseWork_expected_le (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (hinverse : coarseInverseAllowanceFactor (integerParameters N).B
      (initialThresholdQ N) (initialLambda N) ≤ (inputHeight N : ℝ) ^ 8) :
    ComputedPhysicalCoarseBudget source target N
      (computedWidthEnvelope N * computedCoarseWidthOverhead N) :=
  symbolicComputedCoarseWork_expected_le source target N (computedPhysicalCoarseDepth source target N)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2)) hN
    (two_hundred_le_two_pow_thousand.trans hell) hsize rfl rfl rfl (fun _ => rfl)
    (computedFamilyMemoCode_injective source target N (inputHeight N ^ 2) hN
      (two_hundred_le_two_pow_thousand.trans hell))
    (computedFamilyMemoCode_fits source target N (inputHeight N ^ 2) hN hell hsize le_rfl hB) hinverse

 theorem computedPhysicalCoarseWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ComputedPhysicalCoarseBudget source target N ((N + 2 : ℝ) ^ (1 + epsilon)) := by
  filter_upwards [computedWidthEnvelope_coarse_near_linear epsilon hepsilon,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    computed_localOnlineMassBound_word, coarse_inverse_allowance_le_height_eight_eventually]
    with N hw hN hell hB hinverse
  intro source target hsize
  exact symbolicComputedCoarseBudget_mono source target N (computedPhysicalCoarseDepth source target N)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2)) _ _ hw
    (computedPhysicalCoarseWork_expected_le source target N (by omega) hell hsize hB hinverse)

end EditApproximation

end OAI
