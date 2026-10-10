import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ZeroExpression

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
variable {ι : Type*} [DecidableEq ι] {E F : ℕ}
lemma factors_append_subset (d : SquarefreeExpression ι E) (e : SquarefreeExpression ι F)
    (U : Finset ι) (hd : ∀ i, d.factors i ⊆ U) (he : ∀ i, e.factors i ⊆ U) :
    ∀ i, (d.append e).factors i ⊆ U := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j; simpa only [append,Fin.addCases_left] using hd j
  · intro j; simpa only [append,Fin.addCases_right] using he j
end OrdinaryCorrelations.ArithmeticSaving.SquarefreeExpression

end

end OAI
