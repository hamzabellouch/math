import OAI.Combinatorics.EditApproximation.Refinement.ComputedExecutionLaw
import OAI.Combinatorics.EditApproximation.Refinement.ComputedRetainedValues
import OAI.Combinatorics.EditApproximation.Probability.FiniteProductWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open MeasureTheory Filter





 theorem computedFamilyRejectionWork_integrable (source target : List ℕ) (N : ℕ)
    (seed : ComputedFamilySeed source target N) :
    Integrable (fun execution : ComputedRejectionRuntime source target N =>
      computedFamilyRejectionWork source target N (seed, execution))
      (rejectionRuntimeArrayLaw (physicalFamilyRange (M := (integerParameters N).M)
        (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
        target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))) :=
  physicalFamilyMemoBits_integrable source target N (integerParameters N).P
    (integerParameters N).T (integerParameters N).S (inputHeight N) (Nat.two_pow_pos _)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (finalTargetState target.length) seed

 theorem computedExecutionRejectionWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      integral (computedExecutionLaw source target N) (computedExecutionRejectionWork source target N) ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedFamilyRejectionWork_expected_near_linear epsilon hepsilon] with N hN
  intro source target hsize
  let incoming := physicalCoarseSeedLaw (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M source.length) source target N
    (integerParameters N).B (computedPhysicalCoarseDepth source target N)
  have hmap := integral_map (μ := computedExecutionLaw source target N)
    (computedExecutionProjection_measurable source target N).aemeasurable
    (measurable_of_countable (computedFamilyRejectionWork source target N)).aestronglyMeasurable
  rw [computedExecutionProjection_law] at hmap
  change (∫ execution, computedFamilyRejectionWork source target N
    (computedExecutionProjection source target N execution) ∂computedExecutionLaw source target N) ≤ _
  rw [← hmap]
  apply finite_outer_expected_le incoming _ (computedFamilyRejectionWork source target N)
    (computedFamilyRejectionWork_integrable source target N) _
  intro seed
  exact hN source target hsize seed

 theorem computedExecution_requests_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ execution : ComputedExecutionOutcome source target N,
      ((computedFamilyResult source target N (computedExecutionAccepted source target N execution)).requests : ℝ) ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedFamilyResult_requests_near_linear epsilon hepsilon] with N hN
  intro source target hsize execution
  exact hN source target hsize _

 theorem computedExecution_retained_storage (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N) (execution : ComputedExecutionOutcome source target N) :
    (computedFamilyResult source target N (computedExecutionAccepted source target N execution)).memory.rationalStorage ≤
      (N + 2) ^ 65556 :=
  computedFamilyResult_retained_storage source target N hN hell hsize hB _

end EditApproximation

end OAI
