import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalRepresentativeSets
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalPacking

namespace OAI

/-! The packings for the configurations with missing clique vertices. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

private theorem terminal_five_packing_contradiction (hCE : CEAlphaTwo)
    (ht9 : Q.card = 9) (hcycle : ¬ HasCycle G 20) (hclique : G.cliqueNum ≤ Q.card)
    (hbound : IndependenceBound G 19) (hXk : S.ground.card ≤ 19)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      19 * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hpair : ∀ x ∈ S.representativeFinset,
      HasIndependent (G.induce (outsideBallFinset G S.ground x 1 : Set V)) 2)
    (hclass : ∀ x ∈ S.representativeFinset, ∀ y ∈ S.representativeFinset,
      x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 → OutsidePath G (S.ground : Set V) x y d →
      TerminalAlternative S 19 d x y)
    {x₀ y₀ : V} (hfixed : TerminalAlternative S 19 5 x₀ y₀) (hv : S.incident = 4) : False := by
  classical
  have hinc := S.incidentRepresentatives_subset_representatives
  have hincV := S.incidentRepresentatives_subset_vertices
  have hcard := S.incidentRepresentatives_card
  have hRcard : S.representativeFinset.card = 9 := by
    rw [S.representativeFinset_card, ht9]
  have hAcard : S.incidentRepresentatives.card = 4 := by omega
  have htriple : ∀ x ∈ S.representativeFinset,
      HasIndependent (G.induce (outsideBallFinset G S.ground x 2 : Set V)) 3 := by
    intro x hx
    exact outsideBall_two_triple_of_first_pair (k := 19) (t := Q.card)
      (X := S.ground) (x := x) hCE (by omega) (by omega) (by omega)
      hcycle hclique hXk hexpand (hpair x hx)
  have hweight : ∀ x ∈ S.representativeFinset, HasIndependent
      (G.induce (outsideBallFinset G S.ground x
        (if x ∈ S.incidentRepresentatives then 2 else 1) : Set V))
      (if x ∈ S.incidentRepresentatives then 3 else 2) := by
    intro x hx
    by_cases hxa : x ∈ S.incidentRepresentatives
    · convert htriple x hx using 1
      · rw [ite_eq_left hxa]
      · rw [ite_eq_left hxa]
      · exact ite_eq_left hxa
    · convert hpair x hx using 1
      · rw [ite_eq_right hxa]
      · rw [ite_eq_right hxa]
      · exact ite_eq_right hxa
  apply terminal_mixed_packing_contradiction hbound S.representativeFinset_subset_ground
    hinc hRcard hAcard hweight
  intro x hx y hy hxy d hd hd' hout
  have hdb : d ≤ 6 := by split_ifs at hd' <;> omega
  have hc := hclass x hx y hy hxy d hd hdb hout
  have hd5 : d = 5 := (hfixed.parameter_unique (by omega) hc).symm
  have hmiss : x ∉ S.vertices ∧ y ∉ S.vertices := by
    rcases hc with ⟨hd2, _⟩ | ⟨hd3, _⟩ | ⟨_, _, _, _, _, _, hx', hy'⟩
    · omega
    · omega
    · exact ⟨hx', hy'⟩
  have hxnot : x ∉ S.incidentRepresentatives := fun hx' => hmiss.1 (hincV hx')
  have hynot : y ∉ S.incidentRepresentatives := fun hy' => hmiss.2 (hincV hy')
  simp only [hxnot, hynot, ↓reduceIte] at hd'
  omega

theorem terminal_packing_cases_contradiction (hCE : CEAlphaTwo) {k d₀ : ℕ}
    (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k) (hkQ : k ≤ 2 * Q.card + 1)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hbound : IndependenceBound G k) (hXk : S.ground.card ≤ k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hpair : ∀ x ∈ S.representativeFinset,
      HasIndependent (G.induce (outsideBallFinset G S.ground x 1 : Set V)) 2)
    (hclass : ∀ x ∈ S.representativeFinset, ∀ y ∈ S.representativeFinset,
      x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 → OutsidePath G (S.ground : Set V) x y d →
      TerminalAlternative S k d x y)
    (hL : S.amount = k - Q.card) (hde : d₀ * S.assignedCount ≤ S.amount)
    {x₀ y₀ : V} (halt : TerminalAlternative S k d₀ x₀ y₀)
    (hfull : S.incident = Q.card → False) : False := by
  classical
  have hinc := S.incidentRepresentatives_subset_representatives
  have hincV := S.incidentRepresentatives_subset_vertices
  have hincX : S.incidentRepresentatives ⊆ S.ground :=
    fun x hx => S.representativeFinset_subset_ground (hinc hx)
  have hcard := S.incidentRepresentatives_card
  have hmissing := S.missing_card_add_incident
  have hve := S.incident_le_twice_assignedCount
  have hfixed := halt
  rcases halt with ⟨rfl, hv, _⟩ | ⟨rfl, ht', he, hv, _, _, _⟩ |
    ⟨rfl, ht9, hk19, he, hv, _, _, _⟩
  · have hne : (Q \ S.vertices).Nonempty := by
      apply Finset.card_pos.mp
      have hile := S.incident_le
      have hn : S.incident ≠ Q.card := hfull
      omega
    obtain ⟨z, hz⟩ := hne
    have hzV := (Finset.mem_sdiff.mp hz).2
    apply terminal_uniform_packing_contradiction (k := k) (t := Q.card) hCE ht (by omega) hkQ hcycle hclique
      hbound hincX hXk (by omega) hexpand (fun x hx => hpair x (hinc hx))
    intro x hx y hy hxy d hd hd' hout
    have hc := hclass x (hinc hx) y (hinc hy) hxy d hd hd' hout
    have hd2 : d = 2 := (hfixed.parameter_unique ht hc).symm
    rcases hc with ⟨_, _, hcover⟩ | ⟨hd3, _⟩ | ⟨hd5, _⟩
    · have hzxy := hcover hz
      rcases Finset.mem_insert.mp hzxy with rfl | hzxy
      · exact hzV (hincV hx)
      · have hz_eq_y : z = y := Finset.mem_singleton.mp hzxy
        subst z
        exact hzV (hincV hy)
    · omega
    · omega
  · have hzexists : (Q \ S.vertices).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨z, hz⟩ := hzexists
    have hzV := (Finset.mem_sdiff.mp hz).2
    have hzR : z ∈ S.representativeFinset := S.missing_subset_representatives hz
    have hznot : z ∉ S.incidentRepresentatives := fun hz' => hzV (hincV hz')
    let R := insert z S.incidentRepresentatives
    have hRrep : R ⊆ S.representativeFinset := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hzR
      · exact hinc hx
    have hRcard : R.card = Q.card - 2 := by
      rw [Finset.card_insert_of_notMem hznot, hcard]
      omega
    apply terminal_uniform_packing_contradiction (k := k) (t := Q.card) hCE ht (by rcases ht' with ht' | ht' <;> omega)
      hkQ hcycle hclique hbound
      (fun x hx => S.representativeFinset_subset_ground (hRrep hx)) hXk (by omega)
      hexpand (fun x hx => hpair x (hRrep hx))
    intro x hx y hy hxy d hd hd' hout
    have hc := hclass x (hRrep hx) y (hRrep hy) hxy d hd hd' hout
    have hd3 : d = 3 := (hfixed.parameter_unique ht hc).symm
    have hmiss : x ∉ S.vertices ∧ y ∉ S.vertices := by
      rcases hc with ⟨hd2, _⟩ | ⟨_, _, _, _, _, hx', hy'⟩ | ⟨hd5, _⟩
      · omega
      · exact ⟨hx', hy'⟩
      · omega
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxy rfl
      · exact hmiss.2 (hincV hy)
    · exact hmiss.1 (hincV hx)
  · subst k
    exact terminal_five_packing_contradiction hCE ht9 hcycle hclique hbound hXk
      hexpand hpair hclass hfixed hv

end CycleClique.Construction.ExpandedPathSystem

end OAI
