import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeEdgeInjective

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ForestTraversal Finset Classical SimpleGraph
noncomputable section
variable {h ℓ : ℕ}

theorem tree_blocks_with_edges (w : ClosedLine h ℓ) (hh : 0<h) (H : Finset (Fin ℓ))
    (L : ℕ) (hL : 0<L) :
    ∃ bs : List (Block (edgeGraph w hh (w.treeSteps \ H))),
      bs.length ≤ (2*ℓ)/L+2*H.card+1 ∧
      (∀ b ∈ bs,b.walk.length ≤ L) ∧
      (∀ z ∈ treeVertices w,∃ b ∈ bs,z ∈ b.walk.support) ∧
      (∀ e ∈ w.treeSteps \ H,∃ b ∈ bs,treeEdge w e ∈ b.walk.edges) := by
  obtain ⟨p,hplen,hcover,hcount⟩ := grown_tour w hh 0 w.treeSteps (grows_full_tree w)
  obtain ⟨bs,hbs,hbl,hbc⟩ := chunk_cut_cover (edgeGraph w hh (w.treeSteps \ H)) L hL p
  refine ⟨bs,?_,hbl,?_,?_⟩
  · have hcut := tour_cutCount w hh H p hcount
    have hcard : w.treeSteps.card ≤ ℓ := by simpa using card_le_univ w.treeSteps
    have hlen : p.length ≤ 2*ℓ := by rw [hplen]; omega
    exact hbs.trans (Nat.add_le_add_right (Nat.add_le_add (Nat.div_le_div_right hlen) hcut) 1)
  · intro z hz
    exact hbc.1 z (hcover z (reached_full_tree w ▸ hz))
  · intro e he
    apply hbc.2
    · apply List.count_pos_iff.mp
      rw [hcount]
      have hc : 0<(w.treeSteps.filter (fun f => treeEdge w f=treeEdge w e)).card :=
        card_pos.mpr ⟨e,mem_filter.mpr ⟨(mem_sdiff.mp he).1,rfl⟩⟩
      omega
    · exact edgeGraph_adj w hh _ e he

theorem full_tree_blocks (w : ClosedLine h ℓ) (hh : 0<h) (L : ℕ) (hL : 0<L) :
    ∃ bs : List (Block (edgeGraph w hh w.treeSteps)),
      bs.length ≤ (2*ℓ)/L+1 ∧ (∀ b ∈ bs,b.walk.length ≤ L) ∧
      (∀ z ∈ treeVertices w,∃ b ∈ bs,z ∈ b.walk.support) ∧
      (∀ e ∈ w.treeSteps,∃ b ∈ bs,treeEdge w e ∈ b.walk.edges) := by
  obtain ⟨p,hplen,hcover,hcount⟩ := grown_tour w hh 0 w.treeSteps (grows_full_tree w)
  obtain ⟨bs,hbs,hbl,hbc⟩ := chunk_cut_cover (edgeGraph w hh w.treeSteps) L hL p
  have hcut : cutCount (edgeGraph w hh w.treeSteps) p=0 := by
    apply List.countP_eq_zero.mpr
    intro e he hn
    have hnot : e ∉ (edgeGraph w hh w.treeSteps).edgeSet := of_decide_eq_true hn
    exact hnot (p.edges_subset_edgeSet he)
  refine ⟨bs,?_,hbl,?_,?_⟩
  · have hcard : w.treeSteps.card ≤ ℓ := by simpa using card_le_univ w.treeSteps
    have hlen : p.length ≤ 2*ℓ := by rw [hplen]; omega
    rw [hcut,Nat.add_zero] at hbs
    exact hbs.trans (Nat.add_le_add_right (Nat.div_le_div_right hlen) 1)
  · intro z hz
    exact hbc.1 z (hcover z (reached_full_tree w ▸ hz))
  · intro e he
    apply hbc.2
    · apply List.count_pos_iff.mp
      rw [hcount]
      have hc : 0<(w.treeSteps.filter (fun f => treeEdge w f=treeEdge w e)).card :=
        card_pos.mpr ⟨e,mem_filter.mpr ⟨he,rfl⟩⟩
      omega
    · exact edgeGraph_adj w hh _ e he

end
end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
