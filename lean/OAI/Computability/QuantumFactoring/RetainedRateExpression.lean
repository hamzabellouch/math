import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalDataLog
import OAI.Computability.QuantumFactoring.RationalPowerCircuit
import OAI.Computability.QuantumFactoring.RetainedTable
import OAI.Computability.QuantumFactoring.RetainedTotient

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion.Expressions

/-- The exact completed-order success expression.  Its only runtime inputs
are the actual unit order and its totient, both computed from retained rows. -/
def orderRate (n K : ℕ) : RatExpr (Fin 2) :=
  ((RatExpr.ofNat (.var 1)).mul (OrderTrial.Expressions.lambdaE n (.var 0))).repeatedSuccess K

lemma orderRate_value (n K d : ℕ) (hd : d≤2^n) :
    (orderRate n K).eval (fun i : Fin 2=>if i=0 then d else d.totient)=orderSuccess d K := by
  rw [orderRate,RatExpr.repeatedSuccess_value,RatExpr.eval_mul,RatExpr.eval_ofNat,
    OrderTrial.Expressions.lambdaE_correct]
  · simp only [NatExpr.eval,Fin.one_eq_zero_iff,OfNat.ofNat_ne_one,ite_false,ite_true,orderSuccess]
  · simpa only [NatExpr.eval,ite_true] using hd
end Completion.Expressions

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def orderRateVars (t : ℕ) (a m : BooleanNetwork (M.width t) n) :
    Fin 2→BooleanNetwork (M.width t) n :=
  fun i=>if i=0 then M.retainedOrder t a m else M.retainedOrderPhi t a m

lemma orderRateVars_exact {N P d : ℕ} (hn : 2≤n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2≤d) (hdiv : d∣P) (u : (ZMod d)ˣ)
    (ha : ((bitsValue (a.eval (M.encoded x t r))).toNat : ZMod d)=(u : ZMod d))
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (fun i=>(bitsValue ((M.orderRateVars t a m i).eval (M.encoded x t r))).toNat)=
      (fun i : Fin 2=>if i=0 then orderOf u else (orderOf u).totient) := by
  funext i
  dsimp only [orderRateVars]
  split_ifs
  · exact M.retainedOrder_exact hn t a m x r hc hP hP0 hd hdiv u ha hm
  · exact M.retainedOrderPhi_exact hn t a m x r hc hP hP0 hd hdiv u ha hm

lemma retainedOrderRate_exact {N P d : ℕ} (hn : 2≤n) (t K : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2≤d) (hdiv : d∣P) (u : (ZMod d)ˣ)
    (ha : ((bitsValue (a.eval (M.encoded x t r))).toNat : ZMod d)=(u : ZMod d))
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (Completion.Expressions.orderRate n K).eval
      (fun i=>(bitsValue ((M.orderRateVars t a m i).eval (M.encoded x t r))).toNat)=
      Completion.orderSuccess (orderOf u) K := by
  rw [M.orderRateVars_exact hn t a m x r hc hP hP0 hd hdiv u ha hm]
  apply Completion.Expressions.orderRate_value
  have he:=M.retainedOrder_exact hn t a m x r hc hP hP0 hd hdiv u ha hm
  rw [←he]
  exact (bitsValue ((M.retainedOrder t a m).eval (M.encoded x t r))).isLt.le
end NodeMachine
end ExactQuantumFactoring


end

end OAI
