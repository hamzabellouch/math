import OAI.Combinatorics.Crossing.PolygonalChainShortcuts
import OAI.Combinatorics.Crossing.CollinearSegmentUnion

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem adjacent_segments_meet_only_at_bend (a b c : Plane)
    (h : det2 (b-a) (c-b) ≠ 0) {x : Plane}
    (hx : x ∈ segment ℝ a b) (hy : x ∈ segment ℝ b c) : x=b := by
  rw [← Path.range_segment] at hx hy
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  have hs' : segmentPoint a b s.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have ht' : segmentPoint b c t.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have he := segment_intersection_parameters_unique a b b c h s.val t.val 1 0
    (hs'.trans ht'.symm) (by simp)
  rw [he.1,segmentPoint_one] at hs'
  exact hs'.symm

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem minimum_piece_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) : P.vertices (i+1)-P.vertices i ≠ 0 := by
  exact sub_ne_zero.mpr (Ne.symm (P.minimum_vertices_ne hmin i (i+1) (by omega) (by omega)))

theorem minimum_bend_det_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) :
    det2 (P.vertices (i+1)-P.vertices i) (P.vertices (i+2)-P.vertices (i+1)) ≠ 0 := by
  intro he
  apply P.minimum_two_step_not_subset hmin i hi
  exact (collinear_segment_subset_union _ _ _ (P.minimum_vertices_ne hmin i (i+2) (by omega) hi) he).trans
    (Set.union_subset (P.inside i (by omega)) (P.inside (i+1) (by omega)))

theorem minimum_adjacent_intersection (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) {x : Plane}
    (hx : x ∈ segment ℝ (P.vertices i) (P.vertices (i+1)))
    (hy : x ∈ segment ℝ (P.vertices (i+1)) (P.vertices (i+2))) : x=P.vertices (i+1) := by
  exact adjacent_segments_meet_only_at_bend _ _ _ (P.minimum_bend_det_ne_zero hmin i hi) hx hy

end PolygonalChain
end Zarankiewicz

end

end OAI
