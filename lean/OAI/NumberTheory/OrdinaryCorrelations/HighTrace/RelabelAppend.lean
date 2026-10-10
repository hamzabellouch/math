import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ZeroExpression
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
variable {α β : Type*} [DecidableEq α] [DecidableEq β] {E F : ℕ}
lemma relabel_append (d : SquarefreeExpression α E) (f : SquarefreeExpression α F) (e : α ↪ β) :
    (d.append f).relabel e=(d.relabel e).append (f.relabel e) := by
  apply ext_fields
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [factors_relabel,append,Fin.addCases_left,Fin.addCases_right]
  · rfl
lemma relabel_neg (d : SquarefreeExpression α E) (e : α ↪ β) :
    d.neg.relabel e=(d.relabel e).neg := rfl
lemma relabel_zero (e : α ↪ β) :
    (zeroExpression α E).relabel e=zeroExpression β E := by
  apply ext_fields
  · funext i; simp [relabel,zeroExpression]
  · rfl
end OrdinaryCorrelations.ArithmeticSaving.SquarefreeExpression

end

end OAI
