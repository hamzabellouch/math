import Mathlib
import OAI.Computability.QuantumFactoring.VerifiedTreeCompletion
import OAI.Computability.QuantumFactoring.QueueCoverage

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

/-- Projection of the actual retained record, including dummy rows. No true
factorization is used in constructing this projection. -/
def dataLog (x : Basis c) : (t : ℕ)→Trace n t→List (ℕ×List ℕ)
  | 0,_=>[]
  | t+1,h=>
    let q:=M.query.eval (M.config x t h.1)
    ((bitsValue q).toNat,SortedWords.numbers
      (PhysicalTree.nodeWords n (NodeKernel.encoding q h.2)))::dataLog x t h.1
lemma dataLog_length (x : Basis c) (t : ℕ) (h : Trace n t) : (M.dataLog x t h).length=t := by
  induction t with
  | zero=>rfl
  | succ t ih=>simp only [dataLog,List.length_cons,ih]
lemma dataLog_correct (x : Basis c) (t : ℕ) (h : Trace n t) (hv : M.verified x t h) :
    ∀ a∈M.dataLog x t h, a.1=0 ∨ CorrectEncoding a.1 n a.2 := by
  induction t with
  | zero=>simp only [dataLog,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ t ih=>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hv.2
    · exact ih h.1 hv.1 a ha
end NodeMachine
namespace PhysicalTree

lemma verified_query_value {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hv : (machine n).verified (initialQueue n N) t h) :
    (bitsValue ((query n).eval ((machine n).config (initialQueue n N) t h))).toNat=
      (AuxiliaryTree.run t [N]).headD 0 := by
  rw [verified_queue_invariant hn hN hb t h hv]
  have hbounds:=AuxiliaryTree.run_bounds (xs:=[N]) (B:=2^n) (by
    intro a ha
    have he : a=N := by simpa using ha
    subst a
    exact ⟨hN,hb⟩) t
  cases he : AuxiliaryTree.run t [N] with
  | nil=>
    change (bitsValue ((query n).eval (stackEncoding (capacity n) n []))).toNat=0
    rw [query,blockNet_eval,block_stackEncoding]
    simp only [List.getElem?_nil,Option.getD_none,zeroBasis_value]
    rfl
  | cons a as=>
    have ha:=hbounds a (by rw [he];simp)
    change (bitsValue ((query n).eval (stackEncoding (capacity n) n
      (natBasis n a::canonicalWords n as)))).toNat=a
    rw [query_encoding,natBasis_value,Nat.mod_eq_of_lt ha.2]

/-- The labels on the actual verified physical history are exactly the
occurrence-preserving canonical traversal, including its zero padding. -/
lemma verified_dataLog_labels {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hv : (machine n).verified (initialQueue n N) t h) :
    ((machine n).dataLog (initialQueue n N) t h).map Prod.fst=AuxiliaryTree.seen [N] t := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    change (bitsValue ((query n).eval ((machine n).config (initialQueue n N) t h.1))).toNat::
      List.map Prod.fst ((machine n).dataLog (initialQueue n N) t h.1)=_
    rw [verified_query_value hn hN hb t h.1 hv.1,ih h.1 hv.1]
    rfl

/-- Concrete flat complete-data condition sufficient for retrospective lookup:
root present, every required child present, and every non-dummy row a complete
prime factorization. Equal labels from different parents are NOT collapsed. -/
def CompleteLog (n N : ℕ) (rows : List (ℕ×List ℕ)) : Prop :=
  N∈rows.map Prod.fst ∧
  (∀ a∈rows, a.1=0 ∨ CorrectEncoding a.1 n a.2) ∧
  (∀ a∈rows, ∀ d∈AuxiliaryTree.children a.1, d∈rows.map Prod.fst)

theorem verified_complete_log {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (h : NodeMachine.Trace n (2*n^2))
    (hv : (machine n).verified (initialQueue n N) (2*n^2) h) :
    CompleteLog n N ((machine n).dataLog (initialQueue n N) (2*n^2) h) := by
  have he:=verified_dataLog_labels hn hN hb (2*n^2) h hv
  refine ⟨?_,(machine n).dataLog_correct _ _ _ hv,?_⟩
  · rw [he]
    exact AuxiliaryTree.completed_root hN hb
  · intro a ha d hd
    rw [he]
    apply AuxiliaryTree.completed_children hN hb (a:=a.1) _ hd
    rw [←he]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
