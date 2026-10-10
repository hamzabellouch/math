import OAI.Combinatorics.Crossing.MinimumChainVertexPieces
import OAI.Combinatorics.Crossing.OpenSegmentEndpoints
import OAI.Combinatorics.Crossing.DrawingRangeCrossings

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem drawing_chain_piece_open_subset_interior {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) :
    openSegmentTrace (P.vertices i) (P.vertices (i+1)) ⊆ edgeInterior D e := by
  intro x hx
  have hseg := openSegmentTrace_subset_segment _ _ hx
  have hne := openSegmentTrace_ne_endpoints _ _
    (P.minimum_vertices_ne hmin i (i+1) (by omega) (by omega)) x hx
  apply edgeInterior_of_range_not_vertices D e x (P.inside i hi hseg)
  intro j hj
  have hvertex : D.vertex j ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := hj ▸ hseg
  rcases drawing_chain_piece_vertex D e P hmin i hi j hvertex with ⟨he,hii⟩ | ⟨he,hii⟩
  · apply hne.1
    calc
      x = D.vertex j := hj
      _ = D.vertex (.inl e.1) := congrArg D.vertex he
      _ = P.vertices i := by simpa only [hii] using P.first.symm
  · apply hne.2
    calc
      x = D.vertex j := hj
      _ = D.vertex (.inr e.2) := congrArg D.vertex he
      _ = P.vertices (i+1) := by simpa only [hii] using P.last.symm

end Zarankiewicz

end

end OAI
