import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalDataLog
import OAI.Computability.QuantumFactoring.RationalPowerCircuit
import OAI.Computability.QuantumFactoring.CompletionPredicateCircuit
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
open BooleanNetwork BitArithmetic OrderTrial
namespace Completion.Expressions

def orderRateCoin (n K : ℕ) : RatExpr (Fin 3) :=
  ((RatExpr.ofNat (v:=Fin 3) (.var 1)).mul (OrderTrial.Expressions.lambdaE n (.var 0))).repeatedSuccess K
lemma orderRateCoin_value (n K : ℕ) (v : Fin 3→ℕ) (hd : v 0≤2^n) :
    (orderRateCoin n K).eval v=1-(1-(v 1:ℚ)*prescribedMass (v 0))^K := by
  rw [orderRateCoin,RatExpr.repeatedSuccess_value,RatExpr.eval_mul,RatExpr.eval_ofNat,
    OrderTrial.Expressions.lambdaE_correct]
  · rfl
  · exact hd
end Completion.Expressions
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)
abbrev orderVarWidth (n : ℕ) := n+OrderSlots.coinWidth n

def orderFilterVars (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) :
    Fin 3→BooleanNetwork (M.width t) (orderVarWidth n) := fun i=>
  if i=0 then (M.retainedOrder t a m).comp (resizeWord n (orderVarWidth n)) else
  if i=1 then (M.retainedOrderPhi t a m).comp (resizeWord n (orderVarWidth n)) else
  (raw.comp (Completion.retentionWires (OrderSlots.ordinaryWidth n)
    (Completion.transitionWidth n) (2*n) ((n+10)*n^5))).comp
      (resizeWord (OrderSlots.coinWidth n) (orderVarWidth n))

def orderActualFilter (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) ((n+10)*n^5)
    (Completion.Expressions.orderRateCoin n (n^5)) (RatExpr.const (Completion.target n))
    (M.orderFilterVars t a m raw)
    (raw.comp (Completion.rareWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5))) (.var 2)
    (equalOn (OrderSlots.orderResultNet a m (raw.comp (Completion.ordinaryWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))) (M.retainedOrder t a m))
    (equalOn (raw.comp (Completion.guessWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))
      ((M.retainedOrder t a m).comp (resizeWord n (Completion.transitionWidth n))))

def orderDummyFilter (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) ((n+10)*n^5)
    (RatExpr.const 1) (RatExpr.const (Completion.target n)) (M.orderFilterVars t a m raw)
    (raw.comp (Completion.rareWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5))) (.var 2)
    (constant true)
    (zeroWord (raw.comp (Completion.guessWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5))))

def retainedOrderFilter (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  ((OrderSlots.usableOn a m).band (M.orderActualFilter t a m raw)).bor
    ((OrderSlots.usableOn a m).bnot.band (M.orderDummyFilter t a m raw))

lemma orderFilterVars_eval (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n))
    (x : Basis (M.width t)) (r : OrderSlots.Result n)
    (hraw : raw.eval x=OrderSlots.layout n r) :
    (bitsValue ((M.orderFilterVars t a m raw 0).eval x)).toNat=
      (bitsValue ((M.retainedOrder t a m).eval x)).toNat ∧
    (bitsValue ((M.orderFilterVars t a m raw 1).eval x)).toNat=
      (bitsValue ((M.retainedOrderPhi t a m).eval x)).toNat ∧
    (bitsValue ((M.orderFilterVars t a m raw 2).eval x)).toNat=(bitsValue r.2.2.2).toNat := by
  simp only [orderFilterVars,Fin.reduceEq,ite_true,ite_false,eval_comp]
  rw [resizeWord_toNat (by dsimp only [orderVarWidth,OrderSlots.coinWidth]; omega),
    resizeWord_toNat (by dsimp only [orderVarWidth,OrderSlots.coinWidth]; omega),
    resizeWord_toNat (by dsimp only [orderVarWidth,OrderSlots.coinWidth]; omega),hraw]
  change _ ∧ _ ∧ (bitsValue ((Completion.retentionWires _ _ _ _).eval
    (Completion.layout _ _ _ _ (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)))).toNat=_
  rw [Completion.retentionWires_eval]
  exact ⟨rfl,rfl,rfl⟩

lemma orderActualFilter_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (raw : BooleanNetwork (M.width t) (OrderSlots.width n))
    (x : Basis c) (h : Trace n t) (r : OrderSlots.Result n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (u : (ZMod d)ˣ)
    (ha : ((bitsValue (a.eval (M.encoded x t h))).toNat : ZMod d)=(u : ZMod d))
    (hm : (bitsValue (m.eval (M.encoded x t h))).toNat=d)
    (hr : raw.eval (M.encoded x t h)=OrderSlots.layout n r) :
    (M.orderActualFilter t a m raw).eval (M.encoded x t h) 0=true ↔
      Completion.test (fun y=>orderResult (OrderSlots.sampleExponent n) n
        (a.eval (M.encoded x t h)) (m.eval (M.encoded x t h)) (n^5) y=orderOf u)
        (fun y=>y=natBasis _ (orderOf u)) (Completion.orderSuccess (orderOf u) (n^5)) (Completion.target n) r := by
  have hv:=M.orderFilterVars_eval t a m raw (M.encoded x t h) r hr
  have he:=M.retainedOrder_exact hn t a m x h hc hP hP0 hd hdiv u ha hm
  have hf:=M.retainedOrderPhi_exact hn t a m x h hc hP hP0 hd hdiv u ha hm
  unfold orderActualFilter
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
  · exact hv.2.2
  · rw [equalOn_value,he,OrderSlots.orderResultNet_value _ _ _ _ r.2.1]
    · rw [eval_comp,hr]
      exact Completion.ordinaryWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
    · rwa [hm]
  · have heq : ((M.retainedOrder t a m).comp (resizeWord n (Completion.transitionWidth n))).eval (M.encoded x t h)=
        natBasis (Completion.transitionWidth n) (orderOf u) := by
      rw [eval_comp,resizeWord_eq_natBasis,he]
    have hvv : (raw.comp (Completion.guessWires (OrderSlots.ordinaryWidth n)
        (Completion.transitionWidth n) (2*n) ((n+10)*n^5))).eval (M.encoded x t h)=r.2.2.1 := by
      rw [eval_comp,hr]
      exact Completion.guessWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
    rw [equalOn_value,hvv,heq]
    exact ⟨fun hh=>(bitsEquiv _).injective (BitVec.eq_of_toNat_eq hh),congrArg (fun z=>(bitsValue z).toNat)⟩
  · rw [Completion.Expressions.orderRateCoin_value]
    · rw [hv.1,hv.2.1,he,hf]
      rfl
    · rw [hv.1]
      exact (bitsValue ((M.retainedOrder t a m).eval (M.encoded x t h))).isLt.le
  · exact RatExpr.eval_const _ _

lemma orderDummyFilter_exact (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) (x : Basis (M.width t))
    (r : OrderSlots.Result n) (hr : raw.eval x=OrderSlots.layout n r) :
    (M.orderDummyFilter t a m raw).eval x 0=true ↔
      Completion.test (fun _=>True) (fun y=>y=natBasis _ 0) 1 (Completion.target n) r := by
  have hv:=M.orderFilterVars_eval t a m raw x r hr
  unfold orderDummyFilter
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
  · exact hv.2.2
  · simp only [eval_constant]
  · rw [zeroWord_value,eval_comp,hr]
    change (bitsValue ((Completion.guessWires _ _ _ _).eval
      (Completion.layout _ _ _ _ (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)))).toNat=0 ↔ _
    rw [Completion.guessWires_eval]
    exact basis_eq_natBasis (by positivity) _
  · exact RatExpr.eval_const _ _
  · exact RatExpr.eval_const _ _
end NodeMachine
end ExactQuantumFactoring


end

end OAI
