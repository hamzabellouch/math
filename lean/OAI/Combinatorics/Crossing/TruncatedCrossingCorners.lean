import OAI.Combinatorics.Crossing.TruncatedDrawingInteriors
import OAI.Combinatorics.Crossing.ReducedCrossingCorners

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem truncated_vertices_not_crossing (D : AdmissibleDrawing m n)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ)
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e : BipartiteEdge m n) (i : ℕ) (hi : i ≤ (P e).pieces) :
    (P e).truncatedVertices r i ∉ crossingPoints D.toContinuousDrawing := by
  by_cases h0 : i=0
  · subst i
    rw [(P e).truncatedVertices_first]
    intro hx
    have hc := (drawing_chain_startPort_circle D.toContinuousDrawing e (P e) (hmin e) r).le
    exact Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear (.inl e.1)) hc hx
  by_cases hn : i=(P e).pieces
  · subst i
    rw [(P e).truncatedVertices_last (drawing_chain_pieces_pos D.toContinuousDrawing e (P e))]
    intro hx
    have hc := (drawing_chain_endPort_circle D.toContinuousDrawing e (P e) (hmin e) r).le
    exact Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear (.inr e.2)) hc hx
  · simp only [PolygonalChain.truncatedVertices,ite_eq_right h0,ite_eq_right hn]
    exact minimum_vertices_not_crossing D hstraight e (P e) (hmin e) i hi

end Zarankiewicz

end

end OAI
