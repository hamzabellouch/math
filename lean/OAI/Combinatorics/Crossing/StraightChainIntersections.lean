import OAI.Combinatorics.Crossing.DrawnEdgeChains

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
open scoped BigOperators
variable {O T : Set Plane} {a b c d : Plane}

theorem intersection_single_right (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T) :
    polygonIntersection P.vertices (single T c d hc hcd).vertices P.pieces 1=
      ∑ i ∈ Finset.range P.pieces, segmentCrossingSign (P.vertices i) (P.vertices (i+1)) c d := by
  simp [polygonIntersection,single]

theorem intersection_single_left (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T) :
    polygonIntersection (single T c d hc hcd).vertices P.vertices 1 P.pieces=
      ∑ i ∈ Finset.range P.pieces, segmentCrossingSign c d (P.vertices i) (P.vertices (i+1)) := by
  simp [polygonIntersection,single]

theorem transverse_single_right (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T)
    (h : ∀ i : Fin P.pieces, SegmentPairTransverse (P.vertices i.val) (P.vertices (i.val+1)) c d) :
    P.Transverse (single T c d hc hcd) := by
  intro i j
  have hj : j.val=0 := by have hj : j.val<1 := j.isLt; omega
  simpa [single,hj] using h i

theorem transverse_single_left (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T)
    (h : ∀ i : Fin P.pieces, SegmentPairTransverse c d (P.vertices i.val) (P.vertices (i.val+1))) :
    (single T c d hc hcd).Transverse P :=
  P.transverse_swap _ (P.transverse_single_right hc hcd (fun i => segmentPairTransverse_swap _ _ _ _ (h i)))

theorem intersection_single_right_zero (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T)
    (h : ∀ i : Fin P.pieces, ¬ ClosedSegmentsMeet (P.vertices i.val) (P.vertices (i.val+1)) c d) :
    polygonIntersection P.vertices (single T c d hc hcd).vertices P.pieces 1=0 := by
  rw [P.intersection_single_right]
  apply Finset.sum_eq_zero
  intro i hi
  exact segmentCrossingSign_eq_zero_of_not_meet _ _ _ _ (h ⟨i,Finset.mem_range.mp hi⟩)

theorem intersection_single_single (ha : a ∈ O) (hab : segment ℝ a b ⊆ O)
    (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T) :
    polygonIntersection (single O a b ha hab).vertices (single T c d hc hcd).vertices 1 1=
      segmentCrossingSign a b c d := by simp [polygonIntersection,single]

end Zarankiewicz.PolygonalChain

end

end OAI
