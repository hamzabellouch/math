import OAI.Combinatorics.Crossing.VertexDisksCrossingFree
import OAI.Combinatorics.Crossing.TruncatedTraceDecomposition

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem crossing_mem_truncated_edge (D : AdmissibleDrawing m n) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e : BipartiteEdge m n) (x : Plane) (hx : x ∈ crossingPoints D.toContinuousDrawing)
    (hxe : x ∈ edgeInterior D.toContinuousDrawing e) :
    x ∈ Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces) := by
  have hh := edgeInterior_subset_range D.toContinuousDrawing e hxe
  rw [drawing_edge_trace_decomposition D.toContinuousDrawing e (P e) r hr (hshort e).1 (hshort e).2] at hh
  rcases hh with (hs | hm) | ht
  · have hmem := center_segment_in_disk (D.vertex (.inl e.1)) ((P e).startPort r) r
      (drawing_chain_startPort_circle D.toContinuousDrawing e (P e) (hmin e) r) hs
    exact False.elim (Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear (.inl e.1)) hmem hx)
  · exact hm
  · have ht' : x ∈ segment ℝ (D.vertex (.inr e.2)) ((P e).endPort r) := by
      simpa only [segment_symm ℝ ((P e).endPort r) (D.vertex (.inr e.2))] using ht
    have hmem := center_segment_in_disk (D.vertex (.inr e.2)) ((P e).endPort r) r
      (drawing_chain_endPort_circle D.toContinuousDrawing e (P e) (hmin e) r) ht'
    exact False.elim (Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear (.inr e.2)) hmem hx)

end Zarankiewicz

end

end OAI
