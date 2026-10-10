import OAI.Analysis.ModularTheory.CommutantExpectation
import OAI.Analysis.Nuclearity.CPFaithfulRestriction
import OAI.Analysis.TracialSplitting.ChallengeDefinitions

namespace OAI

/-! The finite part of the injectivity argument starts with a hypertrace.
Composing a tracial state with the actual cpc expectation gives that
hypertrace, since the multiplicative-domain calculation is bimodular. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem expectation_hypertrace (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T) :
    ∃ φ : (H →L[ℂ] H) →ₚ[ℂ] ℂ, φ 1 = 1 ∧
      (∀ a : M.toStarSubalgebra, φ a = τ.functional a) ∧
      ∀ (a : M.toStarSubalgebra) (T : H →L[ℂ] H),
        φ ((a : H →L[ℂ] H) * T) = φ (T * (a : H →L[ℂ] H)) := by
  let ι := M.toStarSubalgebra.subtype
  let F : (H →L[ℂ] H) →L[ℂ] M.toStarSubalgebra :=
    E.codRestrict M.toStarSubalgebra.toSubalgebra.toSubmodule hEr
  have hF : CompletelyPositive F := by
    apply completelyPositive_of_faithful_postcomp F ι.toNonUnitalStarAlgHom Subtype.val_injective
    exact hE
  have he (a : M.toStarSubalgebra) : F (ι a) = a := by
    apply Subtype.ext
    exact hEf _ a.property
  let φ : (H →L[ℂ] H) →ₚ[ℂ] ℂ :=
    PositiveLinearMap.mk₀ (τ.functional.toLinearMap.comp F.toLinearMap)
      (fun T hT => τ.functional.map_nonneg (completelyPositive_map_nonneg hF hT))
  refine ⟨φ, ?_, ?_, ?_⟩
  · change τ.functional (F 1) = 1
    have h1 : F 1 = 1 := by simpa only [map_one] using he 1
    rw [h1, τ.normalized]
  · intro a
    change τ.functional (F (ι a)) = τ.functional a
    rw [he]
  · intro a T
    change τ.functional (F (ι a * T)) = τ.functional (F (T * ι a))
    rw [cp_extension_representation_mul_left ι (StarAlgHom.id ℂ M.toStarSubalgebra)
      F hF he, cp_extension_representation_mul_right ι (StarAlgHom.id ℂ M.toStarSubalgebra)
      F hF he]
    exact τ.tracial a (F T)

end WeakPureInfiniteness

end

end OAI
