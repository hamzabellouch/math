import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalMachineMass
import OAI.Computability.QuantumFactoring.TreeHistoryAccess
import OAI.Computability.QuantumFactoring.RetrospectiveNode
import OAI.Computability.QuantumFactoring.SplitHistoryAccess
import OAI.Computability.QuantumFactoring.RetainedSplitPass

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

def nodePrefixFilter (hn : 0<n) (T : ℕ) : (s : ℕ)→
    BooleanNetwork (M.width T) ((PhysicalNode.machine n (2*n)).width s)→BooleanNetwork (M.width T) 1
  | 0,_=>constant true
  | s+1,v=>(nodePrefixFilter hn T s (v.comp ((PhysicalNode.machine n (2*n)).previousNet s))).band
      (M.retainedSplitFilter hn T (v.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s)))

def retainedNodeFilter (hn : 0<n) (T : ℕ)
    (raw : BooleanNetwork (M.width T) (NodeKernel.width n)) : BooleanNetwork (M.width T) 1 :=
  M.nodePrefixFilter hn T (2*n) raw

lemma nodePrefixFilter_passed {N : ℕ} (hn : 128≤n) (T s : ℕ)
    (raw : BooleanNetwork (M.width T) ((PhysicalNode.machine n (2*n)).width s))
    (x : Basis c) (h : Trace n T) (q : Basis n) (r : SplitMachine.Trace n s)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x T h))
    (hq : (bitsValue q).toNat=0 ∨ 2≤(bitsValue q).toNat)
    (hP : (bitsValue q).toNat≠0 → (bitsValue q).toNat∈(M.dataLog x T h).map Prod.fst)
    (hr : raw.eval (M.encoded x T h)=
      (PhysicalNode.machine n (2*n)).encoded (NodeKernel.start q) s r) :
    (M.nodePrefixFilter (by omega) T s raw).eval (M.encoded x T h) 0=true ↔
      (PhysicalNode.machine n (2*n)).passed (NodeKernel.start q) s r := by
  induction s with
  | zero=>simp [nodePrefixFilter,SplitMachine.passed]
  | succ s ih=>
    rw [nodePrefixFilter,eval_band,Bool.and_eq_true]
    apply and_congr
    · apply ih _ r.1
      rw [eval_comp,hr,SplitMachine.previousNet_encoded]
    · have hraw : (raw.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s)).eval
          (M.encoded x T h)= FixedSplit.encoding
          ((PhysicalNode.query n (2*n)).eval ((PhysicalNode.machine n (2*n)).config
            (NodeKernel.start q) s r.1)) r.2 := by
        rw [eval_comp,hr,SplitMachine.lastSplitNet_encoded]
        rfl
      rcases hq with hz | hpos
      · apply M.retainedSplitFilter_nonhard hn T _ _ _ r.2 _ hraw
        have hzero:=PhysicalNode.query_zero hn q hz s r.1
        intro hh
        have hh':=hh.1
        omega
      · apply M.retainedSplitFilter_passed hn T _ x h _ r.2 hc (hP (by omega)) (by omega) _ hraw
        intro hh
        have hs:=PhysicalNode.query_safe hn hpos (bitsValue q).isLt s r.1
        rw [←PhysicalNode.startNet_eval n q] at hs
        change (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat=0 ∨
          (2 ≤ (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat ∧
          (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat<2^n ∧
          (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat∣(bitsValue q).toNat) at hs
        rcases hs with hz | hs
        · have hh':=hh.1
          omega
        · exact hs.2.2

/-- Every split in the actual retained node history is tested against the final
read-only verified table. No fresh random experiment or ideal flag is inserted. -/
theorem retainedNodeFilter_passed {N : ℕ} (hn : 128≤n) (T : ℕ)
    (raw : BooleanNetwork (M.width T) (NodeKernel.width n))
    (x : Basis c) (h : Trace n T) (q : Basis n) (r : NodeKernel.Raw n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x T h))
    (hq : (bitsValue q).toNat=0 ∨ 2≤(bitsValue q).toNat)
    (hP : (bitsValue q).toNat≠0 → (bitsValue q).toNat∈(M.dataLog x T h).map Prod.fst)
    (hr : raw.eval (M.encoded x T h)=NodeKernel.encoding q r) :
    (M.retainedNodeFilter (by omega) T raw).eval (M.encoded x T h) 0=true ↔ NodeKernel.passed q r :=
  M.nodePrefixFilter_passed hn T (2*n) raw x h q r hc hq hP hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI
