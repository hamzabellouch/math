import Mathlib
import OAI.Computability.QuantumFactoring.RetrospectiveNode

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial AuxiliaryTree
namespace PhysicalTree

lemma verified_query_safe {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (r : NodeMachine.Trace n t)
    (hv : (machine n).verified (initialQueue n N) t r) :
    let m:=(bitsValue ((query n).eval ((machine n).config (initialQueue n N) t r))).toNat
    m=0 ∨ 2 ≤ m := by
  dsimp only
  rw [verified_query_value hn hN hb t r hv]
  have hh:=run_bounds (xs:=[N]) (B:=2^n) (by
    intro a ha
    have he : a=N := List.mem_singleton.mp ha
    subst a
    exact ⟨hN,hb⟩) t
  cases he : run t [N] with
  | nil=>exact Or.inl rfl
  | cons a as=>exact Or.inr (hh a (by rw [he];simp)).1
end PhysicalTree
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Read-only postprocessing of the retained actual history. Each node receives
only the flat row data at its actual runtime label. Occurrences are retained;
lookup selects the first matching verified record, not a factorization oracle. -/
noncomputable def dataTests (rows : List (ℕ×List ℕ)) (x : Basis c) (hn : 0<n) :
    (t : ℕ)→Trace n t→Prop
  | 0,_=>True
  | t+1,r=>dataTests rows x hn t r.1 ∧
    let q:=M.query.eval (M.config x t r.1)
    NodeKernel.dataPassed q (PhysicalTree.flatData rows (bitsValue q).toNat) hn r.2
end NodeMachine
namespace PhysicalTree

lemma dataTests_correct {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (rows : List (ℕ×List ℕ)) (hc : CompleteLog n N rows)
    (t : ℕ) (r : NodeMachine.Trace n t)
    (hv : (machine n).verified (initialQueue n N) t r)
    (hr : ∀ a∈(machine n).dataLog (initialQueue n N) t r,a∈rows) :
    (machine n).dataTests rows (initialQueue n N) (by omega) t r ↔
      (machine n).passed (initialQueue n N) t r := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    apply and_congr (ih r.1 hv.1 (fun a ha=>hr a (List.mem_cons_of_mem _ ha)))
    apply NodeKernel.dataPassed_correct hn _ _ (verified_query_safe hn hN hb t r.1 hv.1)
    intro hpos
    apply completeLog_view hc _ hpos
    apply List.mem_map.mpr
    refine ⟨_,hr _ (List.mem_cons_self),rfl⟩

/-- Literal event specification for completed-data retrospective checking.
The Boolean implementation of the arithmetic and the whole polynomial-time
compiler are separate obligations, not consequences of this definition. -/
noncomputable def accepted {n N : ℕ} (hn : 0<n) (r : NodeMachine.Trace n (2*n^2)) : Prop :=
  (machine n).verified (initialQueue n N) (2*n^2) r ∧
    (machine n).dataTests ((machine n).dataLog (initialQueue n N) (2*n^2) r)
      (initialQueue n N) hn (2*n^2) r

/-- Same-history retrospective equivalence, with the actual physical data tree
and actual divisibility-safe node controller. Unverified factor data is rejected
first; no comparison to a counterfactual run is used. -/
theorem accepted_iff_passed {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (r : NodeMachine.Trace n (2*n^2)) :
    accepted (N:=N) (by omega) r ↔ (machine n).passed (initialQueue n N) (2*n^2) r := by
  constructor
  · rintro ⟨hv,hd⟩
    exact (dataTests_correct hn hN hb _ (verified_complete_log hn hN hb r hv)
      _ r hv (fun _ ha=>ha)).mp hd
  · intro hp
    have hv:=passed_verified hn hN hb _ r hp
    exact ⟨hv,(dataTests_correct hn hN hb _ (verified_complete_log hn hN hb r hv)
      _ r hv (fun _ ha=>ha)).mpr hp⟩

/-- Exact accepted mass, after the actual complete-data checks. This is still
an event theorem: using it as a physical phase flag requires the missing fully
assembled retrospective Boolean network, rather than an arbitrary predicate. -/
theorem accepted_mass {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n) :
    Exactness.outcomeMass (accepted (n:=n) (N:=N) (by omega))
      ((machine n).state (initialQueue n N) (2*n^2))=
        (((Completion.target n:ℝ)^(n^5+1))^(2*n))^(2*n^2) := by
  have he : accepted (n:=n) (N:=N) (by omega)=
      (machine n).passed (initialQueue n N) (2*n^2) := by
    funext r
    exact propext (accepted_iff_passed hn hN hb r)
  rw [he]
  exact (machine n).passed_mass hn _ _
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
