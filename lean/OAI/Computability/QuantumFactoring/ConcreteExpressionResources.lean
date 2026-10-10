import Mathlib
import OAI.Computability.QuantumFactoring.PolynomialExpressionResources

namespace OAI



section

namespace ExactQuantumFactoring
namespace PolyExpr
variable {v : Type*}
lemma comp_X (a : PolyExpr v) : a.comp X=a := by
  induction a with
  | C c => rfl
  | X => rfl
  | add a b ia ib => simp only [comp,ia,ib]
  | negation a ia => simp only [comp,ia]
  | mul a b ia ib => simp only [comp,ia,ib]
lemma comp_comp (a b c : PolyExpr v) : (a.comp b).comp c=a.comp (b.comp c) := by
  induction a with
  | C r => rfl
  | X => rfl
  | add a b ia ib => simp only [comp,ia,ib]
  | negation a ia => simp only [comp,ia]
  | mul a b ia ib => simp only [comp,ia,ib]
end PolyExpr

/-- Substitution-stable, fixed-depth polynomial schemas. In particular this
controls the literal syntax of every fixed coefficient, not just its denotation. -/
def PolySchemaPoly {v : ℕ → Type*} (a : ∀ n, PolyExpr (v n)) : Prop :=
  ∀ b : ∀ n, PolyExpr (v n), PolyExprPoly b → PolyExprPoly (fun n => (a n).comp (b n))

end ExactQuantumFactoring
end

end OAI
