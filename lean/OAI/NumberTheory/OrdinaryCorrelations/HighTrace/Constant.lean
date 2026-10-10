import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExtFields

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving.SquarefreeExpression
open Finset Classical
noncomputable section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
def constant (k : ℤ) : SquarefreeExpression α 1 where
  factors _ := ∅
  coefficient _ := k
@[simp] lemma eval_constant (k : ℤ) (x : α → ℤ) : (constant k).eval x=k := by simp [constant,eval]
@[simp] lemma support_constant (k : ℤ) : (constant (α:=α) k).support=∅ := by
  ext p; by_cases hk : k=0 <;> simp [support,constant,hk]
lemma constantExpression_relabel (k : ℤ) (v : α ↪ β) : (constant k).relabel v=constant k := by
  apply ext_fields
  · funext i; simp [relabel,constant]
  · rfl
end
end OrdinaryCorrelations.ArithmeticSaving.SquarefreeExpression

end

end OAI
