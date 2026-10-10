import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SquarefreeExpression

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
variable {ι : Type*} [DecidableEq ι] {E : ℕ}
lemma linearCoeff_zero_of_not_support (d : SquarefreeExpression ι E) (q : ι)
    (hq : q ∉ d.support) (x : ι → ℤ) : d.linearCoeff q x=0 := by
  apply sum_eq_zero
  intro i hi
  by_cases hc : d.coefficient i=0
  · simp [hc]
  · exact ite_eq_right (fun hm => hq (d.mem_support hc hm))
end OrdinaryCorrelations.ArithmeticSaving.SquarefreeExpression

end

end OAI
