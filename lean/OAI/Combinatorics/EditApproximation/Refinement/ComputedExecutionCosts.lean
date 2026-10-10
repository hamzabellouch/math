import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.Combinatorics.EditApproximation.Refinement.ComputedExecutionWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedJointCoarseWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedAddressWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter MeasureTheory

 theorem computedExecutionRejectionWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionRejectionWork source target N) (computedExecutionLaw source target N) := by
  let incoming := physicalCoarseSeedLaw (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M source.length) source target N
    (integerParameters N).B (computedPhysicalCoarseDepth source target N)
  have hi : Integrable (computedFamilyRejectionWork source target N)
      (physicalFamilyRuntimeLaw (R := inputHeight N ^ 2) target N (integerParameters N).P
        (inputHeight N) incoming) :=
    finite_outer_integrable incoming _ (computedFamilyRejectionWork source target N)
      (computedFamilyRejectionWork_integrable source target N)
  have hj : Integrable (computedFamilyRejectionWork source target N)
      ((computedExecutionLaw source target N).map (computedExecutionProjection source target N)) := by
    rw [computedExecutionProjection_law]
    exact hi
  exact hj.comp_measurable (computedExecutionProjection_measurable source target N)

 theorem computedExecutionAccepted_measurable (source target : List ℕ) (N : ℕ) :
    Measurable (computedExecutionAccepted source target N) := measurable_of_countable _

 theorem computedExecutionAcceptedWork_integrable (source target : List ℕ) (N : ℕ)
    (f : ComputedFamilyInput source target N → ℝ) :
    Integrable (f ∘ computedExecutionAccepted source target N) (computedExecutionLaw source target N) := by
  have hi : Integrable f ((computedExecutionLaw source target N).map
      (computedExecutionAccepted source target N)) := Integrable.of_finite
  exact hi.comp_measurable (computedExecutionAccepted_measurable source target N)



 theorem computedExecutionDictionaryWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionDictionaryWork source target N) (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N
    (fun input => (computedFamilyResult source target N input).dictionaryVisits)

 theorem computedExecutionDictionaryWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionDictionaryWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedFamilyResult_dictionary_near_linear epsilon hepsilon] with N hN
  intro source target hsize
  calc
    _ ≤ ∫ _ : ComputedExecutionOutcome source target N, (N + 2 : ℝ) ^ (1 + epsilon)
        ∂computedExecutionLaw source target N :=
      integral_mono (computedExecutionDictionaryWork_integrable source target N) (integrable_const _)
        (fun execution => hN source target hsize _)
    _ = _ := by simp



 theorem computedExecutionAddressWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionAddressWork source target N) (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N
    (fun input => (computedFamilyAddressWork source target N input : ℝ))

 theorem computedExecutionAddressWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionAddressWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedFamilyAddressWork_near_linear epsilon hepsilon] with N hN
  intro source target hsize
  calc
    _ ≤ ∫ _ : ComputedExecutionOutcome source target N, (N + 2 : ℝ) ^ (1 + epsilon)
        ∂computedExecutionLaw source target N :=
      integral_mono (computedExecutionAddressWork_integrable source target N) (integrable_const _)
        (fun execution => hN source target hsize _)
    _ = _ := by simp

/-- These are the actual coarse, rejection-bit, dictionary and address-construction counters.
The local arithmetic counter is kept separate until its kernel is composed. -/


 theorem computedExecutionNonlocalWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionNonlocalWork source target N) (computedExecutionLaw source target N) :=
  (((computedExecutionCoarseWork_integrable source target N).add
    (computedExecutionRejectionWork_integrable source target N)).add
    (computedExecutionDictionaryWork_integrable source target N)).add
    (computedExecutionAddressWork_integrable source target N)

 theorem constant_le_rpow_eventually (C epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, C ≤ (N + 2 : ℝ) ^ epsilon := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  exact ((tendsto_rpow_atTop hepsilon).comp ht).eventually (eventually_ge_atTop C)

 theorem computedExecutionNonlocalWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionNonlocalWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedExecutionCoarseWork_expected_near_linear (epsilon / 2) hhalf,
    computedExecutionRejectionWork_expected_near_linear (epsilon / 2) hhalf,
    computedExecutionDictionaryWork_expected_near_linear (epsilon / 2) hhalf,
    computedExecutionAddressWork_expected_near_linear (epsilon / 2) hhalf,
    constant_le_rpow_eventually 4 (epsilon / 2) hhalf] with N hc hr hd ha hfour
  intro source target hsize
  have hiC := computedExecutionCoarseWork_integrable source target N
  have hiR := computedExecutionRejectionWork_integrable source target N
  have hiD := computedExecutionDictionaryWork_integrable source target N
  have hiA := computedExecutionAddressWork_integrable source target N
  change integral (computedExecutionLaw source target N)
    (((computedExecutionCoarseWork source target N + computedExecutionRejectionWork source target N) +
      computedExecutionDictionaryWork source target N) + computedExecutionAddressWork source target N) ≤ _
  rw [integral_add' ((hiC.add hiR).add hiD) hiA, integral_add' (hiC.add hiR) hiD,
    integral_add' hiC hiR]
  calc
    _ ≤ 4 * (N + 2 : ℝ) ^ (1 + epsilon / 2) := by
      linarith only [hc source target hsize, hr source target hsize, hd source target hsize,
        ha source target hsize]
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
