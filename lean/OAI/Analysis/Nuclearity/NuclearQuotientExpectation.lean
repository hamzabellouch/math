import OAI.Analysis.Nuclearity.NuclearCommutantExpectation

namespace OAI

/-! The commutant projection applies to every representation of a quotient:
precomposition does not change the represented algebra. This transfers the
injectivity input, without assuming nuclearity of the quotient. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace WeakPureInfiniteness

variable {A Q H : Type*} [CStarAlgebra A] [CStarAlgebra Q]
  [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma representationCommutant_quotient (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    representationCommutant (π.comp q) = representationCommutant π := by
  have hr : Set.range (π.comp q) = Set.range π := by
    ext T
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨q a, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := hq x
      exact ⟨a, rfl⟩
  exact congrArg (StarSubalgebra.centralizer ℂ) hr

/-- Every quotient representation has an actual cpc commutant projection. -/
theorem nuclear_quotient_commutant_expectation [Nontrivial H] (hA : Nuclear A)
    (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q) (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ∃ P : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H), CompletelyPositive P ∧ ‖P‖ ≤ 1 ∧
      (∀ T, P T ∈ representationCommutant π) ∧
      (∀ T, T ∈ representationCommutant π → P T = T) := by
  simpa only [representationCommutant_quotient q hq π] using
    nuclear_representation_commutant_expectation hA (π.comp q)

end WeakPureInfiniteness

end

end OAI
