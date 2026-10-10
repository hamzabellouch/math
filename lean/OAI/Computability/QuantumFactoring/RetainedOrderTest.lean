import Mathlib
import OAI.Computability.QuantumFactoring.RetainedOrderFilter
import OAI.Computability.QuantumFactoring.RetrospectiveSlots

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Both actual usable slots and actual dummy slots, with the identical physical
coin and retained guessed string in their respective branches. -/
theorem retainedOrderFilter_exact {N P : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (raw : BooleanNetwork (M.width t) (OrderSlots.width n))
    (x : Basis c) (h : Trace n t) (r : OrderSlots.Result n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ (bitsValue (m.eval (M.encoded x t h))).toNat)
    (hdiv : (bitsValue (m.eval (M.encoded x t h))).toNat∣P)
    (hr : raw.eval (M.encoded x t h)=OrderSlots.layout n r) :
    (M.retainedOrderFilter t a m raw).eval (M.encoded x t h) 0=true ↔
      dataOrderPassed (trueData P) (a.eval (M.encoded x t h)) (m.eval (M.encoded x t h)) r := by
  classical
  rw [retainedOrderFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,OrderSlots.usableOn_value a m _ (by omega),
    dataOrderPassed,residueUsable_iff]
  by_cases hu : OrderSlots.Usable (a.eval (M.encoded x t h)) (m.eval (M.encoded x t h))
  · simp only [hu,ite_eq_left,true_and,not_true_eq_false,false_and,or_false]
    rw [dataOrder_correct (by omega) hd hdiv hu.2.unit hu.2.unit_spec.symm,
      dataOrderSuccess_correct (by omega) hd hdiv hu.2.unit hu.2.unit_spec.symm]
    exact M.orderActualFilter_exact hn t a m raw x h r hc hP hP0 hd hdiv
      hu.2.unit hu.2.unit_spec.symm rfl hr
  · simp only [hu,ite_eq_right,false_and,not_false_eq_true,true_and,false_or]
    exact M.orderDummyFilter_exact t a m raw (M.encoded x t h) r hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI
