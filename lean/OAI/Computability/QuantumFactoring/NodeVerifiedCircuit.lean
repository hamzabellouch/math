import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeQueue
import OAI.Computability.QuantumFactoring.PhysicalTreeMass
import OAI.Computability.QuantumFactoring.TreeHistoryAccess

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

def resultFields (n : ℕ) : Fin n→BooleanNetwork (NodeKernel.width n) n :=
  fun i=>(nodeResult n).comp (tensorSelect n n i)
def nodeWords (n : ℕ) (z : Basis (NodeKernel.width n)) : List (Basis n) :=
  List.ofFn (fun i=>(resultFields n i).eval z)
lemma fields_nodeWords (n : ℕ) (z : Basis (NodeKernel.width n)) :
    (fields n).map (fun a=>a.eval z)=nodeWords n z := by
  rw [fields,List.map_ofFn]
  rfl
lemma nodeWords_length (n : ℕ) (z : Basis (NodeKernel.width n)) : (nodeWords n z).length=n :=
  List.length_ofFn
lemma numbers_nodeWords (n : ℕ) (z : Basis (NodeKernel.width n)) :
    SortedWords.numbers (nodeWords n z)=candidateWords (resultFields n) z := by
  simp only [SortedWords.numbers,nodeWords,candidateWords,List.map_ofFn,Function.comp_def]

def NodeVerified {n : ℕ} (q : Basis n) (r : NodeKernel.Raw n) : Prop :=
  (bitsValue q).toNat=0 ∨ CorrectEncoding (bitsValue q).toNat n
    (SortedWords.numbers (nodeWords n (NodeKernel.encoding q r)))

lemma node_verified_of_passed {n : ℕ} (hn : 128 ≤ n) (q : Basis n)
    (hq : (bitsValue q).toNat=0 ∨ 2 ≤ (bitsValue q).toNat)
    (r : NodeKernel.Raw n) (hp : NodeKernel.passed q r) : NodeVerified q r := by
  rcases hq with hz | ha
  · exact Or.inl hz
  · right
    have hp' : (PhysicalNode.machine n (2*n)).passed
        (NodeStateCircuit.pack [natBasis (n+1) (bitsValue q).toNat] [] false) (2*n) r := by
      simpa only [NodeKernel.passed,NodeKernel.start,PhysicalNode.startNet_eval] using hp
    obtain ⟨zs,hl,hc,he⟩ := PhysicalNode.complete_output hn ha (bitsValue q).isLt r hp'
    have hf : nodeWords n (NodeKernel.encoding q r)=zs := by
      rw [←fields_nodeWords]
      apply fields_eval _ zs hl
      rw [nodeResult,eval_comp,NodeKernel.encoding,SplitMachine.current_encoded,
        NodeKernel.start,PhysicalNode.startNet_eval]
      exact he
    rw [hf]
    exact hc

/-- The queue remains canonical for ANY retrospectively verified local result,
not only for results obtained on the all-good event. -/
theorem update_verified {n : ℕ} (hn : 128 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (ha : 2 ≤ (bitsValue a).toNat)
    (r : NodeKernel.Raw n) (hv : NodeVerified a r) :
    ∃ kids : List (Basis n), SortedWords.numbers kids=AuxiliaryTree.children (bitsValue a).toNat ∧
      (update n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) (NodeKernel.encoding a r))=
        stackEncoding (capacity n) n (kids++as) := by
  rcases hv with hz | hc
  · omega
  · refine ⟨ChildQueue.kids (nodeWords n (NodeKernel.encoding a r)),
      ChildQueue.kids_correct (by omega) ha _ hc,?_⟩
    rw [update_eval (by omega : 2 ≤ n) a as hlen ha,fields_nodeWords]

end PhysicalTree
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def verified (x : Basis c) : (t : ℕ)→Trace n t→Prop
  | 0,_=>True
  | t+1,h=>verified x t h.1 ∧ PhysicalTree.NodeVerified
      (M.query.eval (M.config x t h.1)) h.2

def rowQuery (t : ℕ) : BooleanNetwork (M.width (t+1)) n :=
  ((M.previousNet t).comp (M.currentNet t)).comp M.query
def rowFields (t : ℕ) (i : Fin n) : BooleanNetwork (M.width (t+1)) n :=
  (M.lastNodeNet t).comp (PhysicalTree.resultFields n i)
def rowVerifiedNet (t : ℕ) : BooleanNetwork (M.width (t+1)) 1 :=
  (zeroWord (M.rowQuery t)).bor (factorVerifierOn (M.rowQuery t) (M.rowFields t))
def verifiedNet : (t : ℕ)→BooleanNetwork (M.width t) 1
  | 0=>constant true
  | t+1=>((M.previousNet t).comp (verifiedNet t)).band (M.rowVerifiedNet t)

lemma rowQuery_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.rowQuery t).eval (M.encoded x (t+1) (h,r))=M.query.eval (M.config x t h) := by
  rw [rowQuery,eval_comp,eval_comp,M.previousNet_encoded,M.current_encoded]
lemma rowFields_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) (i : Fin n) :
    (M.rowFields t i).eval (M.encoded x (t+1) (h,r))=
      (PhysicalTree.resultFields n i).eval (NodeKernel.encoding (M.query.eval (M.config x t h)) r) := by
  rw [rowFields,eval_comp,M.lastNodeNet_encoded]
lemma rowVerifiedNet_encoded (hn : 128 ≤ n) (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.rowVerifiedNet t).eval (M.encoded x (t+1) (h,r)) 0=true ↔
      PhysicalTree.NodeVerified (M.query.eval (M.config x t h)) r := by
  rw [rowVerifiedNet,eval_bor,Bool.or_eq_true,zeroWord_value,
    factorVerifierOn_correct hn,M.rowQuery_encoded,PhysicalTree.NodeVerified,
    PhysicalTree.numbers_nodeWords]
  simp only [candidateWords,M.rowFields_encoded]

/-- A literal, bounded Boolean verifier of every actual retained root/node
factor list. No predicate is silently converted to an oracle gate. -/
theorem verifiedNet_encoded (hn : 128 ≤ n) (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.verifiedNet t).eval (M.encoded x t h) 0=true ↔ M.verified x t h := by
  induction t with
  | zero=>simp [verifiedNet,verified]
  | succ t ih=>
    rw [verifiedNet,eval_band,Bool.and_eq_true,eval_comp,M.previousNet_encoded,
      ih,M.rowVerifiedNet_encoded hn]
    rfl

end NodeMachine
end ExactQuantumFactoring


end

end OAI
