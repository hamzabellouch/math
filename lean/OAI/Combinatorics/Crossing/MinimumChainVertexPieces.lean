import OAI.Combinatorics.Crossing.ReducedPolygonalPresentation
import OAI.Combinatorics.Crossing.CutVertexAvoidance

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem PolygonalChain.minimum_vertex_piece_index {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i k : ℕ) (hi : i < P.pieces) (hk : k ≤ P.pieces)
    (hx : P.vertices k ∈ segment ℝ (P.vertices i) (P.vertices (i+1))) : k=i ∨ k=i+1 := by
  have hlow : i ≤ k := by
    by_contra h
    have hki : k < i := by omega
    have hseg : segment ℝ (P.vertices k) (P.vertices (i+1)) ⊆ O :=
      ((convex_segment (𝕜 := ℝ) _ _).segment_subset hx (right_mem_segment ℝ _ _)).trans (P.inside i hi)
    have hh := P.minimum_shortcut_bound hmin k (i+1) (by omega) (by omega)
      (PolygonalChain.single O _ _ (P.vertex_mem k hk) hseg)
    change i+1-k ≤ 1 at hh
    omega
  have hhigh : k ≤ i+1 := by
    by_contra h
    have hik : i+1 < k := by omega
    have hseg : segment ℝ (P.vertices i) (P.vertices k) ⊆ O :=
      ((convex_segment (𝕜 := ℝ) _ _).segment_subset (left_mem_segment ℝ _ _) hx).trans (P.inside i hi)
    have hh := P.minimum_shortcut_bound hmin i k (by omega) hk
      (PolygonalChain.single O _ _ (P.vertex_mem i (by omega)) hseg)
    change k-i ≤ 1 at hh
    omega
  omega

theorem drawing_chain_piece_vertex {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) (j : BipartiteVertex m n)
    (hx : D.vertex j ∈ segment ℝ (P.vertices i) (P.vertices (i+1))) :
    (j=.inl e.1 ∧ i=0) ∨ (j=.inr e.2 ∧ i+1=P.pieces) := by
  obtain ⟨t,ht⟩ := P.inside i hi hx
  rcases drawing_edge_vertex_parameter D e t j ht with ⟨_,he⟩ | ⟨_,he⟩
  · have hx0 : P.vertices 0 ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := by
      simpa only [P.first,he] using hx
    have hh := P.minimum_vertex_piece_index hmin i 0 hi (by omega) hx0
    exact Or.inl ⟨he,by omega⟩
  · have hxN : P.vertices P.pieces ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := by
      simpa only [P.last,he] using hx
    have hh := P.minimum_vertex_piece_index hmin i P.pieces hi (by omega) hxN
    exact Or.inr ⟨he,by omega⟩

end Zarankiewicz

end

end OAI
