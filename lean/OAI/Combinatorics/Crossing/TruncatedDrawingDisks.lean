import OAI.Combinatorics.Crossing.TruncatedRadialEnds

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem truncated_piece_vertex_disk_cases (D : ContinuousDrawing m n)
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
    (j : BipartiteVertex m n) (e : BipartiteEdge m n) (i : Fin (P e).pieces) (x : Plane)
    (hx : x ∈ segment ℝ ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1))) :
    (j=Sum.inl e.1 ∧ x=(P e).startPort r) ∨
      (j=Sum.inr e.2 ∧ x=(P e).endPort r) ∨ r^2 < squaredLength (x-D.vertex j) := by
  have hp := drawing_chain_pieces_pos D e (P e)
  by_cases hfirst : j=Sum.inl e.1 ∧ i.val=0
  · have hh := (P e).truncated_first_exterior (hmin e) hp r hr (hshort e).1 (hshort e).2
      (by simpa only [hfirst.2] using hx)
    rcases Set.mem_insert_iff.mp hh with he | he
    · exact Or.inl ⟨hfirst.1,he⟩
    · right; right
      simpa only [Set.mem_ofPred_eq,(P e).first,hfirst.1] using he
  by_cases hlast : j=Sum.inr e.2 ∧ i.val+1=(P e).pieces
  · have hi : i.val=(P e).pieces-1 := by omega
    have hh := (P e).truncated_last_exterior (hmin e) hp r hr (hshort e).1 (hshort e).2
      (by simpa only [hi,show (P e).pieces-1+1=(P e).pieces by omega] using hx)
    rcases Set.mem_insert_iff.mp hh with he | he
    · exact Or.inr (Or.inl ⟨hlast.1,he⟩)
    · right; right
      simpa only [Set.mem_ofPred_eq,(P e).last,hlast.1] using he
  · right; right
    have hs : r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) := by nlinarith [(hshort e).1,sq_nonneg r]
    have ht : r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
      nlinarith [(hshort e).2,sq_nonneg r]
    have hxi := (P e).truncated_piece_subset r hr hs ht i.val i.isLt hx
    by_contra h
    exact Set.disjoint_left.mp (hclear j e i (fun h => h.elim hfirst hlast)) (le_of_not_gt h) hxi

theorem truncated_path_vertex_disk_cases (D : ContinuousDrawing m n)
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
    (j : BipartiteVertex m n) (e : BipartiteEdge m n) (x : Plane)
    (hx : x ∈ Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces)) :
    (j=Sum.inl e.1 ∧ x=(P e).startPort r) ∨
      (j=Sum.inr e.2 ∧ x=(P e).endPort r) ∨ r^2 < squaredLength (x-D.vertex j) := by
  obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece ((P e).truncatedVertices r) (P e).pieces
    (drawing_chain_pieces_pos D e (P e)) x hx
  exact truncated_piece_vertex_disk_cases D P hmin r hr hshort hclear j e ⟨i,hi⟩ x hxi

end Zarankiewicz

end

end OAI
