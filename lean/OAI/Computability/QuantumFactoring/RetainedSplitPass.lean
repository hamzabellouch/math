import Mathlib
import OAI.Computability.QuantumFactoring.RetainedSplitFilter

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma retainedSplitFilter_nonhard (hn : 128≤n) (t : ℕ)
    (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hh : ¬UniversalSplit.Hard (bitsValue q).toNat)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.retainedSplitFilter (by omega) t raw).eval x 0=true ↔ UniversalSplit.passed q r := by
  classical
  rw [retainedSplitFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,UniversalSplit.hardOn_value hn,
    M.splitModulus_eval t raw x q r hr]
  simp only [hh,false_and,not_false_eq_true,true_and,false_or]
  rw [UniversalSplit.passed,dite_eq_right hh]
  exact M.splitDummyFilter_exact t raw x q r hr

lemma retainedSplitFilter_passed {N P : ℕ} (hn : 128≤n) (t : ℕ)
    (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis c) (h : Trace n t) (q : Basis n) (r : UniversalSplit.Raw n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hdiv : UniversalSplit.Hard (bitsValue q).toNat → (bitsValue q).toNat∣P)
    (hr : raw.eval (M.encoded x t h)=FixedSplit.encoding q r) :
    (M.retainedSplitFilter (by omega) t raw).eval (M.encoded x t h) 0=true ↔
      UniversalSplit.passed q r := by
  classical
  by_cases hh : UniversalSplit.Hard (bitsValue q).toNat
  · rw [M.retainedSplitFilter_exact hn t raw x h q r hc hP hP0 hdiv hr]
    exact dataSplitPassed_correct (by omega) q hh.1 (hdiv hh) (by omega) r
  · exact M.retainedSplitFilter_nonhard hn t raw _ q r hh hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI
