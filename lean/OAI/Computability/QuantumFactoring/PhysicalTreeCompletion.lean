import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeQueue
import OAI.Computability.QuantumFactoring.PhysicalTreeMachine
import OAI.Computability.QuantumFactoring.PhysicalTreeMass
import OAI.Computability.QuantumFactoring.OccurrenceQueue
import OAI.Computability.QuantumFactoring.CanonicalWords

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

def machine (n : ℕ) : NodeMachine n (configWidth n) := ⟨query n,update n⟩
def initialQueue (n N : ℕ) : Basis (configWidth n) :=
  stackEncoding (capacity n) n (canonicalWords n [N])

/-- On the actual all-passed raw history, the literal physical pending queue is
exactly the remaining canonical occurrence preorder. This is a proof invariant,
not a precomputed queue or advice to the circuit. -/
theorem queue_invariant {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hp : (machine n).passed (initialQueue n N) t h) :
    (machine n).config (initialQueue n N) t h=
      stackEncoding (capacity n) n (canonicalWords n (AuxiliaryTree.run t [N])) := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    obtain ⟨h,r⟩ := h
    have hi := ih h hp.1
    have hbounds := AuxiliaryTree.run_bounds (xs:=[N]) (B:=2^n)
      (by
        intro a ha
        have he : a=N := by simpa using ha
        subst a
        exact ⟨hN,hb⟩) t
    have hlen := AuxiliaryTree.run_queue_length (t:=t) hN hb
    rw [NodeMachine.config,NodeMachine.next,hi]
    change (update n).eval (Fin.append _ (NodeKernel.encoding ((query n).eval _) r))=_
    cases he : AuxiliaryTree.run t [N] with
    | nil=>
      change (update n).eval (Fin.append (stackEncoding (capacity n) n []) _)=_
      rw [update_nil,AuxiliaryTree.run_succ_right,he]
      rfl
    | cons m ms=>
      have hm := hbounds m (by rw [he];simp)
      have hv : (bitsValue (natBasis n m)).toNat=m := by rw [natBasis_value,Nat.mod_eq_of_lt hm.2]
      have hc : (natBasis n m::canonicalWords n ms).length ≤ capacity n := by
        rw [he,List.length_cons] at hlen
        simp only [List.length_cons,canonical_length]
        unfold capacity
        omega
      have hr : NodeKernel.passed (natBasis n m) r := by
        have hh := hp.2
        change NodeKernel.passed ((query n).eval ((machine n).config (initialQueue n N) t h)) r at hh
        rw [hi,he] at hh
        change NodeKernel.passed ((query n).eval (stackEncoding (capacity n) n
          (natBasis n m::canonicalWords n ms))) r at hh
        rw [query_encoding] at hh
        exact hh
      obtain ⟨ks,hk,hu⟩ := update_passed hn (natBasis n m) (canonicalWords n ms) hc
        (by rw [hv];exact hm.1) r hr
      have hks : ks=canonicalWords n (AuxiliaryTree.children m) := by
        rw [hv] at hk
        rw [←canonical_numbers ks,hk]
      change (update n).eval (Fin.append (stackEncoding (capacity n) n
        (natBasis n m::canonicalWords n ms))
          (NodeKernel.encoding ((query n).eval (stackEncoding (capacity n) n
            (natBasis n m::canonicalWords n ms))) r))=_
      rw [query_encoding,hu,hks,AuxiliaryTree.run_succ_right,he]
      change stackEncoding (capacity n) n
        (canonicalWords n (AuxiliaryTree.children m)++canonicalWords n ms)=
        stackEncoding (capacity n) n (canonicalWords n (AuxiliaryTree.children m++ms))
      rw [canonical_append]

/-- The full actual tree controller terminates in the source's polynomial
occurrence cap, with no truncation on a passing history. The circuit nevertheless
has fixed worst-case dimensions on all other histories as well. -/
theorem complete {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (h : NodeMachine.Trace n (2*n^2))
    (hp : (machine n).passed (initialQueue n N) (2*n^2) h) :
    (machine n).config (initialQueue n N) (2*n^2) h=stackEncoding (capacity n) n [] := by
  rw [queue_invariant hn hN hb _ h hp,AuxiliaryTree.run_complete hN hb]
  rfl

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
