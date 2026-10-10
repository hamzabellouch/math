import OAI.Combinatorics.Ramsey.CycleClique.Construction.OptimalRepresentatives
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeSuccessor
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeExtraNeighbor
import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathDetour

namespace OAI

/-! Consecutive-step exclusions provide an extra missed neighbour for
each interior representative. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

theorem IsOptimal.interior_representative_extra_neighbor {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) {x : V}
    (hx : x ∈ S.representativeFinset) (hxQ : x ∉ Q) :
    ∃ y ∈ S.ground, y ∉ S.representativeFinset ∧
      ∀ u ∈ outsideBallFinset G S.ground x 0, ¬ G.Adj u y := by
  obtain ⟨l, hl, A, y, B, he, hy⟩ :=
    S.toRaw.completeClique.representative_successor (List.mem_toFinset.mp hx) hxQ
  have hlS : l ∈ S.chains := by
    change l ∈ S.chains ++ (Q \ S.toRaw.vertices).toList.map (fun v => [v]) at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hl
    · obtain ⟨v, hv, hlv⟩ := List.mem_map.mp hl
      have hxL : x ∈ l := by simp [he]
      have hxv : x = v := by simpa [← hlv] using hxL
      have hvQ := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).1
      exact False.elim (hxQ (hxv.symm ▸ hvQ))
  have hyL : y ∈ l := by simp [he]
  have hyS : y ∈ S.vertices := List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨l, hlS, hyL⟩)
  refine ⟨y, Finset.mem_union_right _ hyS, ?_, ?_⟩
  · exact fun h => hy (List.mem_toFinset.mp h)
  · obtain ⟨P, R, hchains⟩ := List.append_of_mem hlS
    have hforbid := hopt.forbidden_one_vertex_edge_detour hk hQk hQ hcycle
      (by simpa [he] using hchains : S.chains = P ++ (A ++ x :: y :: B) :: R)
    have hc : (A ++ x :: y :: B).IsChain G.Adj := he ▸ (S.paths l hlS).2
    have hxy : G.Adj x y := (List.isChain_append_cons_cons.mp hc).2.1
    intro u hu huy
    have hball := mem_outsideBallFinset.mp hu
    have hxu := ((outsideBall_zero (S.representativeFinset_subset_ground hx)).mp hball).1
    apply hforbid
    simpa only [ground, Finset.coe_union] using
      outsidePath_one_of_common_neighbor hxy.ne hxu huy hball.1

theorem IsOptimal.two_interior_nonclique_balls {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (he : 2 ≤ S.assignedCount) :
    ∃ a ∈ S.representativeFinset, ∃ b ∈ S.representativeFinset, a ≠ b ∧
      ¬ G.IsClique (outsideBallFinset G S.ground a 1 : Set V) ∧
      ¬ G.IsClique (outsideBallFinset G S.ground b 1 : Set V) := by
  obtain ⟨a, ha, b, hb, hab, haQ, hbQ⟩ :=
    RawPathSystem.exists_two_outside_completed_representatives S he
  have haR : a ∈ S.representativeFinset := List.mem_toFinset.mpr ha
  have hbR : b ∈ S.representativeFinset := List.mem_toFinset.mpr hb
  have hclique' : G.cliqueNum ≤ S.representativeFinset.card := by
    simpa only [S.representativeFinset_card] using hclique
  have hnonclique : ∀ x ∈ S.representativeFinset, x ∉ Q →
      ¬ G.IsClique (outsideBallFinset G S.ground x 1 : Set V) := by
    intro x hx hxQ
    obtain ⟨y, hyX, hyR, hmiss⟩ := hopt.interior_representative_extra_neighbor hk hQk hQ hcycle hx hxQ
    exact representative_ball_one_not_clique hx S.representativeFinset_subset_ground
      (hopt.ground_card_le hQk) hyX hyR hclique' hexpand
      (fun z hz hne => hopt.representativeFinset_one_exclusion hk hQk hQ hcycle hx hz hne) hmiss
  exact ⟨a, haR, b, hbR, hab, hnonclique a haR haQ, hnonclique b hbR hbQ⟩

end CycleClique.Construction.ExpandedPathSystem

end OAI
