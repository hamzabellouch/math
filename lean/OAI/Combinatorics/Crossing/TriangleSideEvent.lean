import OAI.Combinatorics.Crossing.SegmentSides
import OAI.Combinatorics.Crossing.AffineSideEvents

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

theorem triangle_side_at_first_edge (a b c : Plane) (t : ℝ) :
    orient2 b c (segmentPoint a b t) = (1-t)*orient2 a b c := by
  dsimp [orient2,det2,segmentPoint]
  ring

theorem triangle_other_side_at_first_edge (a b c : Plane) (t : ℝ) :
    orient2 c a (segmentPoint a b t) = t*orient2 a b c := by
  dsimp [orient2,det2,segmentPoint]
  ring

theorem triangle_edge_side_tests (a b c d e : Plane)
    (harea : 0 < orient2 a b c) (hn : det2 (b-a) (e-d) ≠ 0) :
    (0 < orient2 b c (segmentPoint d e (secondIntersectionParameter a b d e)) ↔
      firstIntersectionParameter a b d e < 1) ∧
    (0 < orient2 c a (segmentPoint d e (secondIntersectionParameter a b d e)) ↔
      0 < firstIntersectionParameter a b d e) := by
  rw [← intersection_parameters_eq a b d e hn,
    triangle_side_at_first_edge, triangle_other_side_at_first_edge]
  constructor
  · rw [mul_pos_iff_of_pos_right harea]
    constructor <;> intro h <;> linarith
  · exact mul_pos_iff_of_pos_right harea

theorem segmentCrossingSign_triangle_event (a b c d e : Plane)
    (harea : 0 < orient2 a b c) (hn : det2 (b-a) (e-d) ≠ 0) :
    segmentCrossingSign a b d e =
      if 0 < secondIntersectionParameter a b d e ∧ secondIntersectionParameter a b d e < 1 then
        slopeSign (det2 (b-a) (e-d)) *
          (positiveIndicator (orient2 b c (segmentPoint d e (secondIntersectionParameter a b d e))) *
           positiveIndicator (orient2 c a (segmentPoint d e (secondIntersectionParameter a b d e))))
      else 0 := by
  obtain ⟨hleft,hright⟩ := triangle_edge_side_tests a b c d e harea hn
  rw [segmentCrossingSign, segmentsCrossProperly_iff_parameters a b d e hn]
  simp only [Set.mem_Ioo,positiveIndicator,hleft,hright]
  by_cases hu : 0 < secondIntersectionParameter a b d e ∧ secondIntersectionParameter a b d e < 1
  · by_cases ht0 : 0 < firstIntersectionParameter a b d e <;>
      by_cases ht1 : firstIntersectionParameter a b d e < 1 <;>
      simp [hu,ht0,ht1,slopeSign]
  · simp [hu]

end Zarankiewicz

end

end OAI
