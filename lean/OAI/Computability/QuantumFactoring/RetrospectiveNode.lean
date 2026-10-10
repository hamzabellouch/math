import Mathlib
import OAI.Computability.QuantumFactoring.RetrospectiveSlots
import OAI.Computability.QuantumFactoring.FlatDataView
import OAI.Computability.QuantumFactoring.FlatDataPredicates
import OAI.Computability.QuantumFactoring.PhysicalNodeSafety

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial AuxiliaryTree
namespace PhysicalNode

lemma natBasis_zero (w : ℕ) : natBasis w 0=(fun _=>false) := by
  apply (bitsEquiv w).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue (natBasis w 0)).toNat=(bitsValue (fun _=>false)).toNat
  rw [natBasis_value,zeroBasis_value]
  simp

lemma start_zero {n : ℕ} (q : Basis n) (hq : (bitsValue q).toNat=0) :
    NodeKernel.start q=NodeStateCircuit.pack (s:=2*n) [] [] false := by
  rw [NodeKernel.start,startNet_eval,hq,natBasis_zero,NodeStateCircuit.pack,NodeStateCircuit.pack]
  apply congrArg (fun x=>Fin.append (Fin.append x (stackEncoding (2*n+1) (n+1) [])) (fun _=>false))
  apply block_ext
  intro i
  rw [block_stackEncoding,block_stackEncoding]
  cases he : i.val with
  | zero=>rfl
  | succ j=>rfl

lemma config_zero {n : ℕ} (hn : 128 ≤ n) (q : Basis n) (hq : (bitsValue q).toNat=0)
    (t : ℕ) (r : SplitMachine.Trace n t) :
    (machine n (2*n)).config (NodeKernel.start q) t r=NodeStateCircuit.pack [] [] false := by
  induction t with
  | zero=>exact start_zero q hq
  | succ t ih=>
    change (machine n (2*n)).next ((machine n (2*n)).config (NodeKernel.start q) t r.1) r.2=_
    rw [ih,next_nil hn]

lemma query_zero {n : ℕ} (hn : 128 ≤ n) (q : Basis n) (hq : (bitsValue q).toNat=0)
    (t : ℕ) (r : SplitMachine.Trace n t) :
    (bitsValue ((query n (2*n)).eval
      ((machine n (2*n)).config (NodeKernel.start q) t r))).toNat=0 := by
  rw [config_zero hn q hq,query,eval_comp,NodeStateCircuit.top_pack]
  change (bitsValue ((resizeWord (n+1) n).eval (fun _=>false))).toNat=0
  rw [resizeWord_value,zeroBasis_value]
  simp
end PhysicalNode

lemma dataSplitPassed_zero {n : ℕ} (d : FactorData) (q : Basis n) (hn : 0<n)
    (hq : (bitsValue q).toNat=0) (r : UniversalSplit.Raw n) :
    dataSplitPassed d q hn r ↔ UniversalSplit.passed q r := by
  classical
  have hh : ¬UniversalSplit.Hard (bitsValue q).toNat := by
    rintro ⟨h,_⟩
    omega
  rw [dataSplitPassed,ite_eq_right hh,UniversalSplit.passed,dite_eq_right hh]

namespace NodeKernel
/-- Retrospective evaluation on the actual split trace, with one verified
read-only factor-data view for this physical node. The controller and all query
words are the same ones used by the physical run. -/
noncomputable def dataTests {n : ℕ} (q : Basis n) (d : FactorData) (hn : 0<n) :
    (t : ℕ)→SplitMachine.Trace n t→Prop
  | 0,_=>True
  | t+1,r=>dataTests q d hn t r.1 ∧ dataSplitPassed d
      ((PhysicalNode.query n (2*n)).eval
        ((PhysicalNode.machine n (2*n)).config (start q) t r.1)) hn r.2

lemma dataTests_correct {n : ℕ} (hn : 128 ≤ n) (q : Basis n) (d : FactorData)
    (hq : (bitsValue q).toNat=0 ∨ 2 ≤ (bitsValue q).toNat)
    (hd : (bitsValue q).toNat≠0 → DataView d (bitsValue q).toNat)
    (t : ℕ) (r : SplitMachine.Trace n t) :
    dataTests q d (by omega) t r ↔ (PhysicalNode.machine n (2*n)).passed (start q) t r := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    apply and_congr (ih r.1)
    rcases hq with hz | hm
    · exact dataSplitPassed_zero d _ _ (PhysicalNode.query_zero hn q hz t r.1) r.2
    · have hb : (bitsValue q).toNat<2^n := (bitsValue q).isLt
      have hs:=PhysicalNode.query_safe hn hm hb t r.1
      rw [←PhysicalNode.startNet_eval n q] at hs
      change _ ∨ _ at hs
      rcases hs with hz | hs
      · exact dataSplitPassed_zero d _ _ hz r.2
      · exact (hd (by omega)).splitPassed_correct (by omega) _ hs.1 hs.2.2 (by omega) r.2

noncomputable def dataPassed {n : ℕ} (q : Basis n) (d : FactorData) (hn : 0<n)
    (r : Raw n) : Prop := dataTests q d hn (2*n) r

lemma dataPassed_correct {n : ℕ} (hn : 128 ≤ n) (q : Basis n) (d : FactorData)
    (hq : (bitsValue q).toNat=0 ∨ 2 ≤ (bitsValue q).toNat)
    (hd : (bitsValue q).toNat≠0 → DataView d (bitsValue q).toNat) (r : Raw n) :
    dataPassed q d (by omega) r ↔ passed q r := dataTests_correct hn q d hq hd (2*n) r
end NodeKernel
end ExactQuantumFactoring


end

end OAI
