import OAI.Combinatorics.Crossing.TruncatedCrossingCorners
import OAI.Combinatorics.Crossing.ReducedCrossingTransversality

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segment_parameter_strict_of_avoids_endpoints (a b x : Plane) (S : Set Plane)
    (hx : x ∈ S) (ha : a ∉ S) (hb : b ∉ S) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (he : segmentPoint a b t=x) : t ∈ Set.Ioo (0 : ℝ) 1 := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h,segmentPoint_zero] at he
    exact ha (he.symm ▸ hx)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h,segmentPoint_one] at he
    exact hb (he.symm ▸ hx)
  exact ⟨lt_of_le_of_ne ht.1 ht0.symm,lt_of_le_of_ne ht.2 ht1⟩

theorem truncated_segment_pair_transverse {m n : ℕ} (D : AdmissibleDrawing m n)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D)
    (htrans : LocallyTransverseCrossings D)
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
    (e f : BipartiteEdge m n) (hef : e ≠ f) (i : Fin (P e).pieces) (j : Fin (P f).pieces) :
    SegmentPairTransverse ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1))
      ((P f).truncatedVertices r j.val) ((P f).truncatedVertices r (j.val+1)) := by
  intro s hs t ht he
  let x := segmentPoint ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1)) s
  have hxe : x ∈ segment ℝ ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1)) := by
    rw [← Path.range_segment]
    exact ⟨⟨s,hs⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint,x]⟩
  have hxf : x ∈ segment ℝ ((P f).truncatedVertices r j.val) ((P f).truncatedVertices r (j.val+1)) := by
    rw [← Path.range_segment]
    refine ⟨⟨t,ht⟩,?_⟩
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,x,segmentPoint] using he.symm
  have hie := truncated_range_subset_edgeInterior D.toContinuousDrawing P hmin r hr hshort hclear e
    (polygonalArcPath_piece_subset_range _ _ i.val i.isLt hxe)
  have hif := truncated_range_subset_edgeInterior D.toContinuousDrawing P hmin r hr hshort hclear f
    (polygonalArcPath_piece_subset_range _ _ j.val j.isLt hxf)
  have hcross : x ∈ crossingPoints D.toContinuousDrawing := ⟨e,f,hef,hie,hif⟩
  have hcorner := truncated_vertices_not_crossing D hnorm hstraight P hmin r hclear
  have hsi := segment_parameter_strict_of_avoids_endpoints _ _ x _ hcross
    (hcorner e i.val (by omega)) (hcorner e (i.val+1) (by omega)) s hs rfl
  have hti := segment_parameter_strict_of_avoids_endpoints _ _ x _ hcross
    (hcorner f j.val (by omega)) (hcorner f (j.val+1) (by omega)) t ht he.symm
  refine ⟨?_,hsi,hti⟩
  have hweak (g : BipartiteEdge m n) :
      r^2 < squaredLength ((P g).vertices 1-(P g).vertices 0) ∧
      r^2 < squaredLength ((P g).vertices (P g).pieces-(P g).vertices ((P g).pieces-1)) := by
    constructor <;> nlinarith [(hshort g).1,(hshort g).2,sq_nonneg r]
  have hde := minimum_piece_det_at_crossing D hstraight htrans e f hef (P e) (P f) (hmin e) (hmin f)
    i.val j.val i.isLt j.isLt x hie hif
    ((P e).truncated_piece_subset r hr (hweak e).1 (hweak e).2 i.val i.isLt hxe)
    ((P f).truncated_piece_subset r hr (hweak f).1 (hweak f).2 j.val j.isLt hxf)
  change det2 (trackDirection ((P e).truncatedVertices r) i.val) (trackDirection ((P f).truncatedVertices r) j.val) ≠ 0
  rw [(P e).truncated_direction r i.val i.isLt,(P f).truncated_direction r j.val j.isLt,
    det2_smul_left,det2_smul_right]
  exact mul_ne_zero (ne_of_gt ((P e).truncatedScale_pos r hr (hshort e).1 (hshort e).2 i.val))
    (mul_ne_zero (ne_of_gt ((P f).truncatedScale_pos r hr (hshort f).1 (hshort f).2 j.val)) hde)

end Zarankiewicz

end

end OAI
