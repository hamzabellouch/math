import Mathlib
import OAI.Analysis.Crouzeix.CompleteFinite

namespace OAI

/-! Hilbert Inequality. -/

namespace CrouzeixHilbert

universe u

theorem hilbert (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : Operator H) :
    (Nontrivial H → NonzeroConclusion A) ∧
    (Subsingleton H → ZeroConclusion A) ∧ SharpConstant := by
  exact hilbert_of_finite_matrix_bound finite_matrix_polynomial_bound H A

end CrouzeixHilbert


end OAI
