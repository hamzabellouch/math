import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawReverse
import OAI.Combinatorics.Ramsey.CycleClique.Construction.InteriorRepresentativeGrowth
import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathSystemCounts

namespace OAI

/-! Reversing chains supplies an extra excluded clique neighbour at any
unused clique representative. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

omit [Fintype V] in
theorem terminal_not_representative (S : ExpandedPathSystem G Q) {l : List V}
    (hl : l ∈ S.chains) {q : V} (hq : q ∈ l.getLast?) : q ∉ S.representativeFinset := by
  have hqQ := (S.endpoints l hl).2 q hq
  have hql : q ∈ l := List.mem_of_mem_getLast? hq
  have hqS : q ∈ S.vertices := List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨l, hl, hql⟩)
  intro hrep
  obtain ⟨r, hr, hqr⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hrep)
  obtain ⟨m, hm, her⟩ := List.mem_map.mp hr
  subst r
  have hqm : q ∈ m := (chainRepresentatives_sublist m).subset hqr
  change m ∈ S.chains ++ (Q \ S.toRaw.vertices).toList.map (fun v => [v]) at hm
  rcases List.mem_append.mp hm with hm | hm
  · by_cases hlm : l = m
    · subst m
      have hhead := chainRepresentatives_clique_mem_head (S.no_clique_steps l hl) hqr hqQ
      have hlen := S.nontrivial l hl
      have hne : l ≠ [] := by intro he; simp [he] at hlen
      have hh : l.head hne = q := by
        simpa only [List.head?_eq_some_head hne, Option.mem_some_iff] using hhead
      have ht : l.getLast hne = q := by
        simpa only [List.getLast?_eq_some_getLast hne, Option.mem_some_iff] using hq
      obtain ⟨v, hv⟩ := ((S.paths l hl).1.head_eq_getLast_iff hne).mp (hh.trans ht.symm)
      simp [hv] at hlen
    · exact List.disjoint_left.mp (S.toRaw.disjoint_of_mem hl hm hlm) hql hqm
  · obtain ⟨v, hv, hmv⟩ := List.mem_map.mp hm
    have heq : q = v := by simpa [← hmv] using hqm
    have hvnot := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).2
    exact hvnot (heq ▸ hqS)

theorem IsOptimal.unused_representative_extra_neighbor {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hchains : S.chains ≠ [])
    {x : V} (hxQ : x ∈ Q) (hxS : x ∉ S.vertices) :
    ∃ y ∈ S.ground, y ∉ S.representativeFinset ∧
      ∀ u ∈ outsideBallFinset G S.ground x 0, ¬ G.Adj u y := by
  let l := S.chains.head hchains
  have hl : l ∈ S.chains := List.head_mem hchains
  have hlen := S.nontrivial l hl
  have hne : l ≠ [] := by intro he; simp [he] at hlen
  let q := l.getLast hne
  have hq : q ∈ l.getLast? := List.getLast?_eq_some_getLast hne
  have hqQ := (S.endpoints l hl).2 q hq
  have hqS : q ∈ S.vertices := List.mem_toFinset.mpr
    (List.mem_flatten.mpr ⟨l, hl, List.getLast_mem hne⟩)
  have hqrep := S.terminal_not_representative hl hq
  have hxrep := RawPathSystem.completed_unused_representative S hxQ hxS
  have hqreverse : q ∈ S.toRaw.completeClique.reverseChains.representatives := by
    apply RawPathSystem.reversed_terminal_representative S.toRaw.completeClique
      (List.mem_append_left _ hl : l ∈ S.toRaw.completeClique.chains) hq
  have hvertices : ∀ v ∈ S.toRaw.completeClique.reverseChains.vertices,
      v ∈ Q ∨ v ∈ S.vertices := by
    intro v hv
    rw [RawPathSystem.reverseChains_vertices, RawPathSystem.completeClique_vertices] at hv
    exact (Finset.mem_union.mp hv).symm
  have hxq : x ≠ q := fun h => hxS (h.symm ▸ hqS)
  have hf := hopt.representatives_one_exclusion hk hQk hQ hcycle
    S.toRaw.completeClique.reverseChains (by simp) hvertices hxrep.2 hqreverse hxq
  refine ⟨q, Finset.mem_union_left _ hqQ, hqrep, ?_⟩
  intro u hu huq
  have hball := mem_outsideBallFinset.mp hu
  have hxX : x ∈ S.ground := Finset.mem_union_left _ hxQ
  have hxu := ((outsideBall_zero hxX).mp hball).1
  apply hf
  simpa only [ground, Finset.coe_union] using
    outsidePath_one_of_common_neighbor hxq hxu huq hball.1

theorem IsOptimal.two_unused_nonclique_balls {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (he : S.assignedCount = 1) (ht : 4 ≤ Q.card) :
    ∃ a ∈ S.representativeFinset, ∃ b ∈ S.representativeFinset, a ≠ b ∧
      ¬ G.IsClique (outsideBallFinset G S.ground a 1 : Set V) ∧
      ¬ G.IsClique (outsideBallFinset G S.ground b 1 : Set V) := by
  have hinc := S.incident_eq_two_of_assignedCount_one he
  have hcard := Finset.card_sdiff_add_card_inter Q S.vertices
  have hinter : (Q ∩ S.vertices).card = S.incident := by
    simp [incident, Finset.inter_comm]
  have htwo : 1 < (Q \ S.vertices).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
  have hchains : S.chains ≠ [] := by
    intro hc
    have hraw := S.assignedCount_eq_raw
    simp [hc, rawAssignedCount, he] at hraw
  have hclique' : G.cliqueNum ≤ S.representativeFinset.card := by
    simpa only [S.representativeFinset_card] using hclique
  have hnonclique : ∀ x ∈ Q \ S.vertices,
      x ∈ S.representativeFinset ∧ ¬ G.IsClique (outsideBallFinset G S.ground x 1 : Set V) := by
    intro x hx
    obtain ⟨hxQ, hxS⟩ := Finset.mem_sdiff.mp hx
    have hxR : x ∈ S.representativeFinset := List.mem_toFinset.mpr
      (RawPathSystem.completed_unused_representative S hxQ hxS).1
    obtain ⟨y, hyX, hyR, hmiss⟩ := hopt.unused_representative_extra_neighbor hk hQk hQ hcycle hchains hxQ hxS
    refine ⟨hxR, representative_ball_one_not_clique hxR S.representativeFinset_subset_ground
      (hopt.ground_card_le hQk) hyX hyR hclique' hexpand ?_ hmiss⟩
    exact fun z hz hne => hopt.representativeFinset_one_exclusion hk hQk hQ hcycle hxR hz hne
  exact ⟨a, (hnonclique a ha).1, b, (hnonclique b hb).1, hab,
    (hnonclique a ha).2, (hnonclique b hb).2⟩

end CycleClique.Construction.ExpandedPathSystem

end OAI
