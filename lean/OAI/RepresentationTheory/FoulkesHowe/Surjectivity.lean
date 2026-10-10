import OAI.RepresentationTheory.FoulkesHowe.CanonicalMap
import OAI.RepresentationTheory.FoulkesHowe.Annihilator

namespace OAI

noncomputable section
namespace Problem346

/-- Existence, surjectivity, and uniqueness reduce entirely to the vanishing theorem. -/
theorem canonical_surjective_unique_of_vanishing (a b : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V]
    (hvan : ∀ T : SymmetricMultilinearForm a b V,
      IsSymmetricMultilinearForm a b V T →
      (∀ u : Fin b → V, T (fun _ => symMonomial b V u) = 0) → T = 0) :
    ∃ μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V),
      IsFoulkesMap a b V μ ∧ Function.Surjective μ ∧
      ∀ ν : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V),
        IsFoulkesMap a b V ν → ν = μ := by
  obtain ⟨μ, hμ⟩ := exists_foulkesMap_from_spanning a b V
  exact ⟨μ, hμ, IsFoulkesMap.surjective_of_vanishing a b V μ hμ hvan,
    fun ν hν => IsFoulkesMap.unique a b V hν hμ⟩

end Problem346

end

end OAI
