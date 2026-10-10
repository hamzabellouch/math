import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalDataLog
import OAI.Computability.QuantumFactoring.RationalPowerCircuit
import OAI.Computability.QuantumFactoring.CompletionPredicateCircuit
import OAI.Computability.QuantumFactoring.RetainedFavorable
import OAI.Computability.QuantumFactoring.RetainedFavorableCount

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

def listRateCoin (n K : ℕ) : RatExpr (Fin 3) :=
  ((RatExpr.ofNat (v:=Fin 3) (.var 1)).div
    (RatExpr.ofNat (OrderTrial.Expressions.coveringPow (.var 0) n))).repeatedSuccess K

lemma listRateCoin_value (n K : ℕ) (v : Fin 3→ℕ) (hm : v 0≤2^n) :
    (listRateCoin n K).eval v=1-(1-(v 1:ℚ)/(2:ℚ)^(Nat.clog 2 (v 0)))^K := by
  rw [listRateCoin,RatExpr.repeatedSuccess_value,RatExpr.eval_div,RatExpr.eval_ofNat,
    RatExpr.eval_ofNat,OrderTrial.Expressions.coveringPow_correct]
  · simp only [NatExpr.eval,Nat.cast_pow,Nat.cast_ofNat]
  · exact hm
end Completion.Expressions

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

abbrev listCoinWidth (n : ℕ) := Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5)
abbrev listVarWidth (n : ℕ) := n+listCoinWidth n

def listFilterVars (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) :
    Fin 3→BooleanNetwork (M.width t) (listVarWidth n) := fun i=>
  if i=0 then m.comp (resizeWord n (listVarWidth n)) else
  if i=1 then (M.retainedFavorableCount t m).comp (resizeWord n (listVarWidth n)) else
  (raw.comp (Completion.retentionWires (PhysicalListSlots.ordinaryWidth n)
    (Completion.transitionWidth n) (2*n) (n*n^5))).comp (resizeWord (listCoinWidth n) (listVarWidth n))

def retainedListFilter (hn : 0<n) (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) (n*n^5)
    (Completion.Expressions.listRateCoin n (n^5)) (RatExpr.const (Completion.target n))
    (M.listFilterVars t m raw)
    (raw.comp (Completion.rareWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))) (.var 2)
    (M.retainedGoodList t m ((raw.comp (Completion.ordinaryWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))).comp (PhysicalListSlots.ordinaryNet n)))
    (M.retainedCanonicalList hn t m (raw.comp (Completion.guessWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))))

lemma listFilterVars_eval (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n))
    (x : Basis (M.width t)) (r : PhysicalListSlots.Result n)
    (hraw : raw.eval x=PhysicalListSlots.layout n r) :
    (bitsValue ((M.listFilterVars t m raw 0).eval x)).toNat=(bitsValue (m.eval x)).toNat ∧
    (bitsValue ((M.listFilterVars t m raw 1).eval x)).toNat=
      (bitsValue ((M.retainedFavorableCount t m).eval x)).toNat ∧
    (bitsValue ((M.listFilterVars t m raw 2).eval x)).toNat=(bitsValue r.2.2.2).toNat := by
  simp only [listFilterVars,Fin.reduceEq,ite_true,ite_false,eval_comp]
  simp only [resizeWord_toNat (show n ≤ listVarWidth n from Nat.le_add_right _ _),
    resizeWord_toNat (show listCoinWidth n ≤ listVarWidth n from Nat.le_add_left _ _),hraw]
  change _ ∧ _ ∧ (bitsValue ((Completion.retentionWires _ _ _ _).eval (Completion.layout _ _ _ _ r))).toNat=_
  rw [Completion.retentionWires_eval]
  exact ⟨True.intro,True.intro,rfl⟩

/-- Concrete local same-history test: the only inputs are the physical retained
words and the complete verified table, not an assumed success oracle. -/
theorem retainedListFilter_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n))
    (x : Basis c) (h : Trace n t) (r : PhysicalListSlots.Result n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (ho : Odd d)
    (hm : (bitsValue (m.eval (M.encoded x t h))).toNat=d)
    (hr : raw.eval (M.encoded x t h)=PhysicalListSlots.layout n r) :
    (M.retainedListFilter (by omega) t m raw).eval (M.encoded x t h) 0=true ↔
      dataListPassed (trueData P) (m.eval (M.encoded x t h)) (by omega) r := by
  have hv:=M.listFilterVars_eval t m raw (M.encoded x t h) r hr
  have hf:=M.retainedFavorableCount_exact hn t m x h hc hP hP0 hd hdiv ho hm
  unfold retainedListFilter dataListPassed
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval r
  · exact hv.2.2
  · rw [M.retainedGoodList_exact hn t m _ x h hc hP hP0 hd hdiv hm]
    erw [eval_comp,eval_comp,hr]
    change dataGoodList (trueData P) d n
      ((PhysicalListSlots.ordinaryNet n).eval ((Completion.ordinaryWires _ _ _ _).eval
        (Completion.layout _ _ _ _ r))) ↔ _
    rw [Completion.ordinaryWires_eval,PhysicalListSlots.ordinaryNet_eval,hm]
  · rw [M.retainedCanonicalList_exact hn t m _ x h hc hP hP0 hd hdiv hm]
    erw [eval_comp,hr]
    change dataCanonicalList (trueData P) d n _
      ((Completion.guessWires _ _ _ _).eval (Completion.layout _ _ _ _ r)) ↔ _
    rw [Completion.guessWires_eval,hm]
  · rw [Completion.Expressions.listRateCoin_value]
    · rw [hv.1,hv.2.1,hf,hm]
      rfl
    · rw [hv.1]
      exact (bitsValue (m.eval (M.encoded x t h))).isLt.le
  · exact RatExpr.eval_const _ _
end NodeMachine
end ExactQuantumFactoring


end

end OAI
