import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.CenteredCodegreeNeighborSum
import OAI.Combinatorics.TriangleRemoval.Spectral.ExtendStarMulVec

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical Matrix

namespace SharpTerminalLeave

lemma extended_link_mulVec_neighbor {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v : neighbors G u) (z : G → ℝ) :
    (extendStar (edgeStar G u) (linkStarMatrix G hG u) *ᵥ z) (neighborEdge G u v).val =
      ∑ w : neighbors G u, if {v.val,w.val} ∈ G then z (neighborEdge G u w).val else 0 := by
  rw [extendStar_mulVec_apply,dite_eq_left (neighborEdge G u v).property]
  simp only [Matrix.mulVec,dotProduct,linkStarMatrix,Matrix.reindex_apply,Matrix.submatrix_apply]
  rw [← Equiv.sum_comp (neighborEdgeEquiv G hG u)]
  have hev : (⟨(neighborEdge G u v).val,(neighborEdge G u v).property⟩ : edgeStar G u) =
      neighborEdgeEquiv G hG u v := rfl
  rw [hev]
  simp only [Equiv.symm_apply_apply,SimpleGraph.adjMatrix_apply,linkSimpleGraph_adj]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs <;> simp only [one_mul,zero_mul]
  rfl

lemma neighbor_filtered_sum {n : ℕ} (G : Graph n) (u v : Fin n) (f : Fin n → ℝ) :
    (∑ w : neighbors G u, if {v,w.val} ∈ G then f w.val else 0) =
      ∑ w ∈ commonNeighbors G u v, f w := by
  trans ∑ w ∈ neighbors G u, if {v,w} ∈ G then f w else 0
  · exact Finset.sum_coe_sort (neighbors G u) (fun w : Fin n => if {v,w} ∈ G then f w else 0)
  rw [← Finset.sum_filter]
  congr 1
  ext w
  simp [neighbors,mem_commonNeighbors]

lemma extended_link_codegree_action {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v : neighbors G u) (s : ℝ) :
    (extendStar (edgeStar G u) (linkStarMatrix G hG u) *ᵥ
      (fun e : G => (triangleDegree G e.val : ℝ)/s-1)) (neighborEdge G u v).val =
      ∑ w ∈ commonNeighbors G u v.val, ((currentCodegree G u w : ℝ)/s-1) := by
  rw [extended_link_mulVec_neighbor]
  have he : (fun w : neighbors G u =>
      if {v.val,w.val} ∈ G then (triangleDegree G (neighborEdge G u w).val.val : ℝ)/s-1 else 0) =
      (fun w : neighbors G u => if {v.val,w.val} ∈ G then (currentCodegree G u w.val : ℝ)/s-1 else 0) := by
    funext w
    simp only [neighborEdge,triangleDegree_eq_codegree hG (Finset.mem_filter.mp w.property).2]
  rw [he]
  exact neighbor_filtered_sum G u v.val (fun w => (currentCodegree G u w : ℝ)/s-1)

lemma global_link_codegree_action {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u v : Fin n) (he : {u,v} ∈ G) (s : ℝ) (hs : s ≠ 0) :
    (globalLinkAdjacency G hG *ᵥ (fun e : G => (triangleDegree G e.val : ℝ)/s-1)) ⟨{u,v},he⟩ =
      centeredCodegreeNeighborSum G u v s/s := by
  have huv := edge_pair_ne hG he
  let z : G → ℝ := fun e => (triangleDegree G e.val : ℝ)/s-1
  have hz : ∀ a : Fin n, a ∉ ({u,v} : Finset (Fin n)) →
      (extendStar (edgeStar G a) (linkStarMatrix G hG a) *ᵥ z) ⟨{u,v},he⟩ = 0 := by
    intro a ha
    rw [extendStar_mulVec_apply,dite_eq_right]
    simpa only [mem_edgeStar] using ha
  have heq : (globalLinkAdjacency G hG *ᵥ z) ⟨{u,v},he⟩ =
      ∑ a ∈ ({u,v} : Finset (Fin n)),
        (extendStar (edgeStar G a) (linkStarMatrix G hG a) *ᵥ z) ⟨{u,v},he⟩ := by
    rw [globalLinkAdjacency,Matrix.sum_mulVec,Finset.sum_apply]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hz a ha)).symm
  change (globalLinkAdjacency G hG *ᵥ z) _ = _
  rw [heq,Finset.sum_pair huv]
  have hvG : ({v,u} : Finset (Fin n)) ∈ G := by simpa only [Finset.pair_comm] using he
  have huact := extended_link_codegree_action G hG u
    (⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩ : neighbors G u) s
  have hvact := extended_link_codegree_action G hG v
    (⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvG⟩⟩ : neighbors G v) s
  change (extendStar (edgeStar G u) (linkStarMatrix G hG u) *ᵥ z) ⟨{u,v},he⟩ = _ at huact
  have hev : (⟨{v,u},hvG⟩ : G) = ⟨{u,v},he⟩ := Subtype.ext (Finset.pair_comm _ _)
  change (extendStar (edgeStar G v) (linkStarMatrix G hG v) *ᵥ z) ⟨{v,u},hvG⟩ = _ at hvact
  rw [hev] at hvact
  rw [huact,hvact]
  have hcn : commonNeighbors G v u = commonNeighbors G u v := by
    ext w; simp [mem_commonNeighbors,and_comm]
  rw [hcn,← Finset.sum_add_distrib,centeredCodegreeNeighborSum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  field_simp
  ring

end SharpTerminalLeave
end
end

end OAI
