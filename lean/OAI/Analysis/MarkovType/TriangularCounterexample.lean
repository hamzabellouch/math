import OAI.Analysis.MarkovType.TriangularCompletion
import OAI.Analysis.MarkovType.TriangularNonreflexivity
import Mathlib.Tactic.Push

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem triangular_family_of_not_obstruction (h : ¬ FiniteTriangularObstruction X) :
    ∃ (θ : ℝ), 0 < θ ∧ θ < 1 ∧ Nonempty (∀ n : ℕ, TriangularSystem X n θ) := by
  classical
  unfold FiniteTriangularObstruction at h
  push Not at h
  obtain ⟨θ, hθ, hθ1, hall⟩ := h
  let s : ∀ n : ℕ, TriangularSystem X n θ := fun n =>
    (Classical.choice (hall (n + 1) (Nat.zero_lt_succ n))).restrict (Nat.le_succ n)
  exact ⟨θ, hθ, hθ1, ⟨s⟩⟩

namespace TriangularLimit

theorem not_canonicallyReflexive {θ : ℝ}
    (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    ¬ CanonicallyReflexive (Space s hθ) :=
  not_canonicallyReflexive_of_triangular_dense
    (basis s hθ) (norm_basis_le s hθ) (tail s hθ) (norm_tail_le s hθ)
    hθ (pairing s hθ) (dense_span_basis s hθ)

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
