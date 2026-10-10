import OAI.Combinatorics.Crossing.VertexPieceClearance
import OAI.Combinatorics.Crossing.ChainTracePieces

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem exists_vertex_trace_disks (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces) :
    ∃ r : ℝ, 0 < r ∧
      (∀ j k, j ≠ k → Disjoint (closedRoundDisk (D.vertex j) r) (closedRoundDisk (D.vertex k) r)) ∧
      (∀ j e x, x ∈ closedRoundDisk (D.vertex j) r →
        (x ∈ Set.range (D.edge e) ↔
          (j=Sum.inl e.1 ∧ x ∈ segment ℝ ((P e).vertices 0) ((P e).vertices 1)) ∨
          (j=Sum.inr e.2 ∧ x ∈ segment ℝ ((P e).vertices ((P e).pieces-1)) ((P e).vertices (P e).pieces)))) := by
  classical
  obtain ⟨r,hr,hdis,hclear⟩ := exists_vertex_piece_clearance D P hmin
  refine ⟨r,hr,hdis,?_⟩
  intro j e x hxd
  have hpos := drawing_chain_pieces_pos D e (P e)
  constructor
  · intro hx
    rw [← drawing_chain_range_eq D e (P e)] at hx
    obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (P e).vertices (P e).pieces hpos x hx
    have hinc : (j=Sum.inl e.1 ∧ i=0) ∨ (j=Sum.inr e.2 ∧ i+1=(P e).pieces) := by
      by_contra h
      exact Set.disjoint_left.mp (hclear j e ⟨i,hi⟩ h) hxd hxi
    rcases hinc with ⟨hj,hii⟩ | ⟨hj,hii⟩
    · exact Or.inl ⟨hj,by simpa only [hii] using hxi⟩
    · have hlast : i=(P e).pieces-1 := by omega
      exact Or.inr ⟨hj,by simpa only [hlast,show (P e).pieces-1+1=(P e).pieces by omega] using hxi⟩
  · rintro (⟨hj,hx⟩ | ⟨hj,hx⟩)
    · exact (P e).inside 0 hpos hx
    · have hi : (P e).pieces-1 < (P e).pieces := by omega
      apply (P e).inside ((P e).pieces-1) hi
      simpa only [show (P e).pieces-1+1=(P e).pieces by omega] using hx

end Zarankiewicz

end

end OAI
