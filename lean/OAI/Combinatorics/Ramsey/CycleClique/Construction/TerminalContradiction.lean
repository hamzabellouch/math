import OAI.Combinatorics.Ramsey.CycleClique.Construction.InteriorSelectionPacking
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalProfileMinimum
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalPackingCases
import OAI.Combinatorics.Ramsey.CycleClique.Construction.ShortRepresentativePath

namespace OAI

/-! Manuscript Proposition terminal:contradiction, conditional only on the
published Chvátal–Erdős alpha-two Hamiltonicity input. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

theorem IsOptimal.terminal_contradiction (hCE : CEAlphaTwo) {k : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hbound : IndependenceBound G k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) : False := by
  obtain ⟨x, hx, y, hy, hxy, d, hd, hd', hout⟩ :=
    hopt.short_representative_path hCE (by omega) ht hQk hkQ hQ hcycle hclique hbound hexpand
  obtain ⟨hxQ, hyQ, hL, hde, halt⟩ := hopt.terminal_finset_classification
    ht hQk hkQ hQ hcycle (by omega) hd' hx hy hxy hout
  obtain ⟨w, hw, hwmin⟩ := hopt.terminal_completed_profile_minimum ht hQk hkQ hQ hcycle
    (by omega) hd' (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hxQ hyQ hxy
    (by simpa only [ground, Finset.coe_union] using hout)
  have hmin : ∀ a ∈ w, 2 ≤ a := fun a ha => (by have hh := hwmin a ha; omega)
  have hc : 2 ≤ S.chains.length := by
    have hcount := S.assignedCount_add_chains_length
    rcases halt with ⟨hd2, hv, _⟩ | ⟨hd3, ht', he, hv, _⟩ |
      ⟨hd5, ht9, _, he, hv, _⟩
    · subst d
      exact S.two_chains_of_terminal_two ht hkQ hL hde hv
    · rcases ht' with ht' | ht' <;> omega
    · omega
  have hfirst : ∀ z ∈ S.representativeFinset,
      HasIndependent (G.induce (outsideBallFinset G S.ground z 1 : Set V)) 2 := by
    intro z hz
    exact (hopt.terminal_first_ball (by omega) hQk hQ hcycle hclique hc
      (fun v => by simpa using hexpand {v} (by simp) (by simp)) hz).2
  have hclass : ∀ x ∈ S.representativeFinset, ∀ y ∈ S.representativeFinset,
      x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 → OutsidePath G (S.ground : Set V) x y d →
      TerminalAlternative S k d x y := by
    intro x hx y hy hne d hd hd' hp
    exact (hopt.terminal_finset_classification ht hQk hkQ hQ hcycle hd hd' hx hy hne hp).2.2.2.2
  have hfull : S.incident = Q.card → False := by
    intro hi
    exact hopt.terminal_spanning_interior_contradiction hCE ht hQk hkQ hQ hcycle
      hclique hbound hc hexpand hw hmin hi
  exact terminal_packing_cases_contradiction hCE ht hQk hkQ hcycle hclique hbound
    (hopt.ground_card_le hQk) hexpand hfirst hclass hL hde halt hfull

end CycleClique.Construction.ExpandedPathSystem

end OAI
