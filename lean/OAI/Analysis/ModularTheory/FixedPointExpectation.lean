import OAI.Analysis.ModularTheory.AmplifiedModularAction
import OAI.Analysis.ModularTheory.RightContinuity
import OAI.Analysis.OperatorAlgebra.UnitaryMeanExpectation
import OAI.Analysis.ModularTheory.FiniteStates

namespace OAI

/-! The concrete cpc fixed-point projection for the modular right action.
It fixes the entire crossed product. The converse fixed-point inclusion
is deliberately not assumed or concluded here. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ComplexOrder CStarAlgebra

namespace WeakPureInfiniteness
open KirchbergRordam.GenericRW.GroupedFactors

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

theorem nuclear_quotient_modular_fixedPoint_expectation
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : BoundedRecovery.StandardModularData H)
    (hS : S.M = bicommutant π.range) :
    ∃ Q : (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) →L[ℂ]
        (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)),
      CompletelyPositive Q ∧ ‖Q‖ ≤ 1 ∧
      (∀ T, Q T ∈ amplifiedModularAlgebra volume S) ∧
      (∀ T s f, Q T (modularRightTranslation volume S.D s f) =
        modularRightTranslation volume S.D s (Q T f)) ∧
      (∀ T, T ∈ modularCrossedProduct volume S → Q T = T) := by
  let : Nontrivial (Lp H 2 (volume : Measure ℝ)) :=
    nontrivial_of_ne (modularCoreWeightVector S (0 + 1)) 0
      (modularCoreWeightVector_succ_ne_zero S 0)
  obtain ⟨E, hE, hEn, hEr, hEf⟩ := nuclear_quotient_amplified_expectation volume hA q hq π S hS
  obtain ⟨Q, hQ, hQn, hQr, hQc, hQf⟩ := realAction_fixedPoint_expectation ω hω
    (modularRightTranslationEquiv volume S.D)
    (modularRightTranslation_continuous S.D)
    (fun t s f => (modularRightTranslation_comp volume S.D t s f).symm)
    (amplifiedModularAlgebra volume S) E hE hEn hEr hEf
    (amplifiedModularAlgebra_invariant volume S)
  refine ⟨Q, hQ, hQn, hQr, hQc, ?_⟩
  intro T hT
  exact hQf T (modularCore_mem_amplification volume S T hT)
    (modularCore_fixed_right volume S T hT)

end WeakPureInfiniteness

end

end OAI
