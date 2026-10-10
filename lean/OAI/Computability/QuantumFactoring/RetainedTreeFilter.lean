import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeLaunch
import OAI.Computability.QuantumFactoring.RetainedNodeFilter
import OAI.Computability.QuantumFactoring.RetrospectiveTree

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

def treePrefixFilter (hn : 0<n) (T : ℕ) : (s : ℕ)→
    BooleanNetwork (M.width T) (M.width s)→BooleanNetwork (M.width T) 1
  | 0,_=>constant true
  | s+1,v=>(treePrefixFilter hn T s (v.comp (M.previousNet s))).band
      (M.retainedNodeFilter hn T (v.comp (M.lastNodeNet s)))

def acceptedNet (hn : 0<n) (T : ℕ) : BooleanNetwork (M.width T) 1 :=
  (M.verifiedNet T).band (M.treePrefixFilter hn T T (select id))
end NodeMachine
namespace PhysicalTree

lemma treePrefixFilter_passed {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (T s : ℕ) (h : NodeMachine.Trace n T) (r : NodeMachine.Trace n s)
    (raw : BooleanNetwork ((machine n).width T) ((machine n).width s))
    (hc : CompleteLog n N ((machine n).dataLog (initialQueue n N) T h))
    (hv : (machine n).verified (initialQueue n N) s r)
    (hsub : ∀ a∈(machine n).dataLog (initialQueue n N) s r,
      a∈(machine n).dataLog (initialQueue n N) T h)
    (hr : raw.eval ((machine n).encoded (initialQueue n N) T h)=
      (machine n).encoded (initialQueue n N) s r) :
    ((machine n).treePrefixFilter (by omega) T s raw).eval
      ((machine n).encoded (initialQueue n N) T h) 0=true ↔
      (machine n).passed (initialQueue n N) s r := by
  induction s with
  | zero=>simp [NodeMachine.treePrefixFilter,NodeMachine.passed]
  | succ s ih=>
    rw [NodeMachine.treePrefixFilter,eval_band,Bool.and_eq_true]
    apply and_congr
    · apply ih r.1 _ hv.1 (fun a ha=>hsub a (List.mem_cons_of_mem _ ha))
      rw [eval_comp,hr,NodeMachine.previousNet_encoded]
    · apply (machine n).retainedNodeFilter_passed hn T _ (initialQueue n N) h _ r.2 hc
        (verified_query_safe hn hN hb s r.1 hv.1)
      · intro _
        apply List.mem_map.mpr
        refine ⟨_,hsub _ (List.mem_cons_self),rfl⟩
      · rw [eval_comp,hr,NodeMachine.lastNodeNet_encoded]
        rfl

/-- A fully assembled same-history Boolean flag on the actual physical tree.
Completeness of the factor table is derived from its literal verification;
it is not a hypothesis of this flag specification. -/
theorem acceptedNet_iff_passed {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (h : NodeMachine.Trace n (2*n^2)) :
    ((machine n).acceptedNet (by omega) (2*n^2)).eval
      ((machine n).encoded (initialQueue n N) (2*n^2) h) 0=true ↔
      (machine n).passed (initialQueue n N) (2*n^2) h := by
  rw [NodeMachine.acceptedNet,eval_band,Bool.and_eq_true,(machine n).verifiedNet_encoded hn]
  constructor
  · rintro ⟨hv,hf⟩
    exact (treePrefixFilter_passed hn hN hb (2*n^2) (2*n^2) h h (select id)
      (verified_complete_log hn hN hb h hv) hv (fun _ ha=>ha) (by rfl)).mp hf
  · intro hp
    have hv:=passed_verified hn hN hb (2*n^2) h hp
    refine ⟨hv,?_⟩
    exact (treePrefixFilter_passed hn hN hb (2*n^2) (2*n^2) h h (select id)
      (verified_complete_log hn hN hb h hv) hv (fun _ ha=>ha) (by rfl)).mpr hp

lemma acceptedNet_iff_accepted {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (h : NodeMachine.Trace n (2*n^2)) :
    ((machine n).acceptedNet (by omega) (2*n^2)).eval
      ((machine n).encoded (initialQueue n N) (2*n^2) h) 0=true ↔ accepted (N:=N) (by omega) h :=
  (acceptedNet_iff_passed hn hN hb h).trans (accepted_iff_passed hn hN hb h).symm
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
