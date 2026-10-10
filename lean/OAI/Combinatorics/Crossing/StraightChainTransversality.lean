import OAI.Combinatorics.Crossing.StraightChainIntersections

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
open scoped BigOperators
variable {O T : Set Plane} {a b c d : Plane}

theorem transverse_single_single (ha : a ∈ O) (hab : segment ℝ a b ⊆ O)
    (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T) (h : SegmentPairTransverse a b c d) :
    (single O a b ha hab).Transverse (single T c d hc hcd) := by
  intro i j
  have hi : i.val=0 := by have hh : i.val<1 := i.isLt; omega
  have hj : j.val=0 := by have hh : j.val<1 := j.isLt; omega
  simpa [single,hi,hj] using h

theorem intersection_single_left_zero (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T)
    (h : ∀ i : Fin P.pieces, ¬ ClosedSegmentsMeet c d (P.vertices i.val) (P.vertices (i.val+1))) :
    polygonIntersection (single T c d hc hcd).vertices P.vertices 1 P.pieces=0 := by
  rw [P.intersection_single_left]
  apply Finset.sum_eq_zero
  intro i hi
  exact segmentCrossingSign_eq_zero_of_not_meet _ _ _ _ (h ⟨i,Finset.mem_range.mp hi⟩)

end Zarankiewicz.PolygonalChain

end

end OAI
