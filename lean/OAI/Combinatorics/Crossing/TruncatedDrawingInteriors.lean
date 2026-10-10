import OAI.Combinatorics.Crossing.TruncatedCrossingRetention

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem truncated_range_subset_edgeInterior (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e : BipartiteEdge m n) :
    Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces) ⊆ edgeInterior D e := by
  intro x hx
  have hs : r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) := by nlinarith [(hshort e).1,sq_nonneg r]
  have ht : r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
    nlinarith [(hshort e).2,sq_nonneg r]
  apply edgeInterior_of_range_not_vertices D e x
  · exact ((P e).truncated (drawing_chain_pieces_pos D e (P e)) r hr hs ht).path_range_subset hx
  · intro j he
    rcases truncated_path_vertex_disk_cases D P hmin r hr hshort hclear j e x hx with ⟨hj,hp⟩ | ⟨hj,hp⟩ | hout
    · have hpi := drawing_chain_startPort_interior D e (P e) (hmin e) r hr hs
      exact edgeInterior_not_vertex D e _ hpi j (hp.symm.trans he)
    · have hpi := drawing_chain_endPort_interior D e (P e) (hmin e) r hr ht
      exact edgeInterior_not_vertex D e _ hpi j (hp.symm.trans he)
    · rw [he,sub_self] at hout
      have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
      rw [hz] at hout
      exact (sq_nonneg r).not_gt hout

theorem truncated_edge_intersections_eq (D : AdmissibleDrawing m n) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e f : BipartiteEdge m n) (hef : e ≠ f) :
    Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces) ∩
      Set.range (polygonalArcPath ((P f).truncatedVertices r) (P f).pieces) =
      edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f := by
  have hweak (g : BipartiteEdge m n) :
      r^2 < squaredLength ((P g).vertices 1-(P g).vertices 0) ∧
      r^2 < squaredLength ((P g).vertices (P g).pieces-(P g).vertices ((P g).pieces-1)) := by
    constructor <;> nlinarith [(hshort g).1,(hshort g).2,sq_nonneg r]
  ext x
  constructor
  · rintro ⟨hx,hy⟩
    exact ⟨truncated_range_subset_edgeInterior D.toContinuousDrawing P hmin r hr hshort hclear e hx,
      truncated_range_subset_edgeInterior D.toContinuousDrawing P hmin r hr hshort hclear f hy⟩
  · rintro ⟨hx,hy⟩
    have hc : x ∈ crossingPoints D.toContinuousDrawing := ⟨e,f,hef,hx,hy⟩
    exact ⟨crossing_mem_truncated_edge D hnorm P hmin r hr hweak hclear e x hc hx,
      crossing_mem_truncated_edge D hnorm P hmin r hr hweak hclear f x hc hy⟩

end Zarankiewicz

end

end OAI
