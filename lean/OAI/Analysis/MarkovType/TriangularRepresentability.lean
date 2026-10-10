import OAI.Analysis.MarkovType.TriangularCoordinateEmbeddings
import OAI.Analysis.MarkovType.FiniteRepresentation
import OAI.Analysis.MarkovType.TriangularCounterexample

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TriangularLimit

theorem finitelyRepresentable {θ : ℝ}
    (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    FinitelyRepresentable (Space s hθ) X :=
  finitelyRepresentable_completion_of_coordinates (limitNorm s) (definite s hθ)
    (coordinate_embeddings s hθ)

end TriangularLimit

theorem exists_nonreflexive_finitelyRepresentable_of_not_obstruction
    (h : ¬ FiniteTriangularObstruction X) :
    ∃ (θ : ℝ) (hθ : 0 < θ) (s : ∀ n : ℕ, TriangularSystem X n θ),
      FinitelyRepresentable (TriangularLimit.Space s hθ) X ∧
        ¬ CanonicallyReflexive (TriangularLimit.Space s hθ) := by
  obtain ⟨θ, hθ, _hθ1, ⟨s⟩⟩ := triangular_family_of_not_obstruction h
  exact ⟨θ, hθ, s, TriangularLimit.finitelyRepresentable s hθ,
    TriangularLimit.not_canonicallyReflexive s hθ⟩

end MarkovSuperreflexivity

end

end OAI
