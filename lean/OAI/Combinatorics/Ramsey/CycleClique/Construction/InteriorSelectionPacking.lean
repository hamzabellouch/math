import OAI.Combinatorics.Ramsey.CycleClique.Construction.InteriorOrientations
import OAI.Combinatorics.Ramsey.CycleClique.Construction.InteriorDetour
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OrientedTerminalWeights
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalRepresentatives
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalPacking

namespace OAI

/-! The selected internal vertices form a separated packing. In a
spanning terminal system they already contradict the independence bound. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

private theorem original_chain_in_completion {l : List V} (hl : l ∈ S.chains) :
    l ∈ S.toRaw.completeClique.chains := by
  exact List.mem_append_left _ hl

theorem selectedChains_outside {w : List ℕ} (h : SystemAssignedAmounts Q S.chains w)
    (hmin : ∀ a ∈ w, 2 ≤ a) : ∀ x ∈ selectedChains Q S.chains, x ∉ Q := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
  obtain ⟨wl, hwl, hsub⟩ := h.profile_of_mem hl
  exact selectedChain_outside hwl (fun a ha => hmin a (hsub a ha)) (S.no_clique_steps l hl) x hx

theorem selectedChains_orientation {w : List ℕ} (h : SystemAssignedAmounts Q S.chains w)
    (hmin : ∀ a ∈ w, 2 ≤ a) {x : V} (hx : x ∈ selectedChains Q S.chains) :
    ∃ p : List V → Bool, x ∈ (S.toRaw.completeClique.orientChains p).representatives := by
  obtain ⟨a, ha, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
  obtain ⟨wl, hwl, hsub⟩ := h.profile_of_mem hl
  obtain ⟨b, hb⟩ := selectedChain_orientation hwl (fun a ha => hmin a (hsub a ha)) hx
  exact ⟨fun _ => b, S.toRaw.completeClique.representative_of_oriented_chain _
    (original_chain_in_completion hl) hb⟩

theorem IsOptimal.selectedChains_forbidden {k : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) {w : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w) (hmin : ∀ a ∈ w, 2 ≤ a)
    {x y : V} (hx : x ∈ selectedChains Q S.chains) (hy : y ∈ selectedChains Q S.chains)
    (hne : x ≠ y) {d : ℕ} (hd : 1 ≤ d) (hd' : d ≤ 6) :
    ¬ OutsidePath G (S.ground : Set V) x y d := by
  intro hout
  have hout' : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d := by
    simpa only [ground, Finset.coe_union] using hout
  obtain ⟨a, ha, hxl⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hb, hym⟩ := List.mem_flatten.mp hy
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hb
  obtain ⟨wl, hwl, hsubl⟩ := h.profile_of_mem hl
  obtain ⟨wm, hwm, hsubm⟩ := h.profile_of_mem hm
  have hminl : ∀ a ∈ wl, 2 ≤ a := fun a ha => hmin a (hsubl a ha)
  have hminm : ∀ a ∈ wm, 2 ≤ a := fun a ha => hmin a (hsubm a ha)
  have hcontra (p : List V → Bool)
      (hx' : x ∈ (S.toRaw.completeClique.orientChains p).representatives)
      (hy' : y ∈ (S.toRaw.completeClique.orientChains p).representatives) : False := by
    have hQx := (hopt.terminal_completed_classification ht hQk hkQ hQ hcycle
      hd hd' p hx' hy' hne hout').1
    exact selectedChains_outside h hmin x hx hQx
  by_cases hlm : l = m
  · subst m
    by_cases hlen : l.length = 4
    · obtain ⟨q, u, v, r, rfl, hq, hr, hu, hv⟩ :=
        hwl.amount_two_shape (amount_profile_eq_two_of_length_four hwl hlen hminl)
      have hx' : x = u ∨ x = v := by simpa [selectedChain] using hxl
      have hy' : y = u ∨ y = v := by simpa [selectedChain] using hym
      obtain ⟨P, R, hsys⟩ := List.append_of_mem hl
      have hf := hopt.forbidden_amount_two_detour ht hQk hkQ hQ hcycle hd hd'
        (A := []) (B := []) (by simpa using hsys) hq hr hu hv
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
      · exact hne rfl
      · exact hf hout'
      · exact hf hout'.reverse
      · exact hne rfl
    · have hx' : x ∈ chainRepresentatives Q l := by
        apply List.mem_of_mem_tail
        simpa [selectedChain, hlen, interiorRepresentatives] using hxl
      have hy' : y ∈ chainRepresentatives Q l := by
        apply List.mem_of_mem_tail
        simpa [selectedChain, hlen, interiorRepresentatives] using hym
      apply hcontra (fun _ => false)
      · exact S.toRaw.completeClique.representatives_orientChains_unchanged
          (original_chain_in_completion hl) rfl hx'
      · exact S.toRaw.completeClique.representatives_orientChains_unchanged
          (original_chain_in_completion hl) rfl hy'
  · obtain ⟨bx, hbx⟩ := selectedChain_orientation hwl hminl hxl
    obtain ⟨by_, hby⟩ := selectedChain_orientation hwm hminm hym
    obtain ⟨p, hp, hp'⟩ := S.toRaw.completeClique.joint_orientation
      (original_chain_in_completion hl) (original_chain_in_completion hm) hlm bx by_ hbx hby
    exact hcontra p hp hp'

variable [Fintype V]

theorem IsOptimal.terminal_spanning_interior_contradiction (hCE : CEAlphaTwo) {k : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hbound : IndependenceBound G k) (hc : 2 ≤ S.chains.length)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    {w : List ℕ} (h : SystemAssignedAmounts Q S.chains w) (hmin : ∀ a ∈ w, 2 ≤ a)
    (hincident : S.incident = Q.card) : False := by
  let R := (selectedChains Q S.chains).toFinset
  have hlarge : Q.card - 1 ≤ R.card := by
    rw [List.toFinset_card_of_nodup S.selectedChains_nodup]
    exact S.selectedChains_large h hmin hincident (by have hb := hopt.budget; omega)
  have hRX : R ⊆ S.ground := by
    intro x hx
    exact Finset.mem_union_right _ (S.selectedChains_mem_vertices (List.mem_toFinset.mp hx))
  have hpair : ∀ x ∈ R,
      HasIndependent (G.induce (outsideBallFinset G S.ground x 1 : Set V)) 2 := by
    intro x hx
    obtain ⟨p, hp⟩ := selectedChains_orientation h hmin (List.mem_toFinset.mp hx)
    exact (hopt.terminal_oriented_first_ball (by omega) hQk hQ hcycle hclique hc
      (fun v => by simpa using hexpand {v} (by simp) (by simp)) p hp).2
  apply terminal_uniform_packing_contradiction hCE ht (by
    have hlen := h.length_eq
    have hsum := h.sum_eq
    have hb := twice_length_le_sum hmin
    have hc' := S.incident_le_twice_assignedCount
    rw [hincident] at hc'
    rw [← S.assignedCount_eq_raw] at hlen
    have hsum' : w.sum = S.amount := by exact hsum.trans S.toRaw.amount_eq_outside_count.symm
    have hbudget := hopt.budget
    omega) hkQ hcycle hclique hbound hRX (hopt.ground_card_le hQk)
    (by omega) hexpand hpair
  intro x hx y hy hne d hd hd'
  exact hopt.selectedChains_forbidden ht hQk hkQ hQ hcycle h hmin
    (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hne hd hd'

end CycleClique.Construction.ExpandedPathSystem

end OAI
