import OAI.Combinatorics.Crossing.TriangleOrientations

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem polygon_intersection_zero_of_cone (v w : ℕ → Plane) (n m : ℕ)
    (hv : v n = v 0) (hw : w m = w 0) (o : Plane)
    (ha : ∀ i ∈ Finset.range n, orient2 o (v i) (v (i+1)) ≠ 0)
    (hp : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range m,
      TriangleSegmentPosition o (v i) (v (i+1)) (w j) (w (j+1))) :
    polygonIntersection v w n m = 0 := by
  unfold polygonIntersection
  calc
    _ = ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n,
        segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1)) := Finset.sum_comm
    _ = ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n,
        triangleSegmentIntersection o (v i) (v (i+1)) (w j) (w (j+1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (polygon_cone_cancellation v n hv o _ _).symm
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        triangleSegmentIntersection o (v i) (v (i+1)) (w j) (w (j+1)) := Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact triangle_closed_walk_intersection_zero o _ _ (ha i hi) w m hw (hp i hi)

end Zarankiewicz

end

end OAI
