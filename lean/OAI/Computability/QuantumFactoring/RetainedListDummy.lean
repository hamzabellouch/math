import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeMachine
import OAI.Computability.QuantumFactoring.CompletionPredicateCircuit
import OAI.Computability.QuantumFactoring.RetainedListFilter

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

def listDummyFilter (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) (n*n^5)
    (RatExpr.const 1) (RatExpr.const (Completion.target n)) (M.listFilterVars t m raw)
    (raw.comp (Completion.rareWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))) (.var 2)
    (constant true)
    (zeroWord (raw.comp (Completion.guessWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))))

lemma listDummyFilter_exact (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) (x : Basis (M.width t))
    (r : PhysicalListSlots.Result n) (hr : raw.eval x=PhysicalListSlots.layout n r) :
    (M.listDummyFilter t m raw).eval x 0=true ↔ UniversalSplit.dummyList r := by
  have hv:=M.listFilterVars_eval t m raw x r hr
  have hh : Completion.test (fun _=>True) (fun y=>y=natBasis _ 0) 1 (Completion.target n) r ↔
    UniversalSplit.dummyList r := Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) r
  refine Iff.trans ?_ hh
  unfold listDummyFilter
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval r
  · exact hv.2.2
  · simp only [eval_constant]
  · rw [zeroWord_value,eval_comp,hr]
    change (bitsValue ((Completion.guessWires _ _ _ _).eval
      (Completion.layout _ _ _ _ r))).toNat=0 ↔ _
    rw [Completion.guessWires_eval]
    exact basis_eq_natBasis (by positivity) _
  · exact RatExpr.eval_const _ _
  · exact RatExpr.eval_const _ _
end NodeMachine
end ExactQuantumFactoring


end

end OAI
