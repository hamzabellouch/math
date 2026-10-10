import OAI.Combinatorics.Ramsey.CycleClique.Construction.InteriorOrientations
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalRepresentatives

namespace OAI

/-! Recover the lower bound on every original assigned amount from an
actual classified short path between completed representatives. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

namespace SystemAssignedAmounts

theorem minimum_of_subset {C D : List (List V)} {W : List ℕ} {d : ℕ}
    (h : SystemAssignedAmounts Q D W) (hmin : ∀ a ∈ W, d ≤ a)
    (hsub : ∀ l ∈ C, l ∈ D) :
    ∃ w, SystemAssignedAmounts Q C w ∧ ∀ a ∈ w, d ≤ a := by
  induction C with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons l C ih =>
    obtain ⟨a, ha, hamin⟩ := h.profile_of_mem (hsub l (by simp))
    obtain ⟨w, hw, hwmin⟩ := ih (fun l hl => hsub l (by simp [hl]))
    refine ⟨a ++ w, .cons ha hw, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hmin x (hamin x hx)
    · exact hwmin x hx

end SystemAssignedAmounts

theorem chainRepresentatives_clique_head {l : List V} {x : V}
    (hsteps : l.IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)))
    (hx : x ∈ chainRepresentatives Q l) (hxQ : x ∈ Q) : ∃ B, l = x :: B := by
  cases l with
  | nil => simp [chainRepresentatives] at hx
  | cons a B =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨B, rfl⟩
    · exact False.elim (representativesFrom_outside hsteps x hx hxQ)

namespace ExpandedPathSystem

variable {S : ExpandedPathSystem G Q}

theorem complete_tail_nil_iff (S : ExpandedPathSystem G Q) {x : V} {B : List V}
    (hl : x :: B ∈ S.toRaw.completeClique.chains) : B = [] ↔ x ∉ S.vertices := by
  apply S.oriented_complete_tail_nil_iff (fun _ => false)
  simpa [RawPathSystem.orientChains, RawPathSystem.orientedChain] using hl

theorem IsOptimal.terminal_completed_profile_minimum {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    {x y : V} (hx : x ∈ S.toRaw.completeClique.representatives)
    (hy : y ∈ S.toRaw.completeClique.representatives) (hxQ : x ∈ Q) (hyQ : y ∈ Q)
    (hne : x ≠ y) (hout : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d) :
    ∃ w, SystemAssignedAmounts Q S.chains w ∧ ∀ a ∈ w, d ≤ a := by
  let U := S.toRaw.completeClique
  obtain ⟨a, ha, hxa⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
  obtain ⟨B, rfl⟩ := chainRepresentatives_clique_head (U.no_clique_steps l hl) hxa hxQ
  obtain ⟨b, hb, hyb⟩ := List.mem_flatten.mp hy
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hb
  obtain ⟨D, rfl⟩ := chainRepresentatives_clique_head (U.no_clique_steps m hm) hyb hyQ
  have hBD : x :: B ≠ y :: D := fun he => hne (List.cons.inj he).1
  obtain ⟨R, hp⟩ := U.bring_two_front hl hm hBD
  let U' := U.reorder ((x :: B) :: (y :: D) :: R) hp
  have hvertices : ∀ v ∈ U'.vertices, v ∈ Q ∨ v ∈ S.vertices := by
    intro v hv
    rw [RawPathSystem.reorder_vertices, RawPathSystem.completeClique_vertices] at hv
    exact (Finset.mem_union.mp hv).symm
  obtain ⟨_, ⟨w, hw, hmin⟩, _⟩ := hopt.terminal_starting_classification ht hQk hkQ hQ hcycle hd hd'
    U' (by simp [U', U]) (by simp [U', U]) (by simp [U', U]) hvertices
    (P := []) (M := []) (R := R) rfl (S.complete_tail_nil_iff hl) (S.complete_tail_nil_iff hm) hne hout
  apply hw.minimum_of_subset hmin
  intro l hl
  change l ∈ (x :: B) :: (y :: D) :: R
  apply hp.mem_iff.mpr
  exact List.mem_append_left _ hl

end ExpandedPathSystem

end CycleClique.Construction

end OAI
