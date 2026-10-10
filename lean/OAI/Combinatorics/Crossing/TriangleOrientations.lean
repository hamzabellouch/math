import OAI.Combinatorics.Crossing.TriangleTransversality

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical

theorem orient2_reverse_edge (a b c : Plane) : orient2 b a c = -orient2 a b c := by
  dsimp [orient2,det2]
  ring

theorem det2_reverse_edge (a b c d : Plane) : det2 (a-b) (d-c) = -det2 (b-a) (d-c) := by
  dsimp [det2]
  ring

theorem triangle_position_reverse (a b c d e : Plane)
    (h : TriangleSegmentPosition a b c d e) : TriangleSegmentPosition a c b d e := by
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i
    · change det2 (c-a) (e-d) ≠ 0
      rw [det2_reverse_edge c a d e]
      exact neg_ne_zero.mpr (h.1 2)
    · change det2 (b-c) (e-d) ≠ 0
      rw [det2_reverse_edge b c d e]
      exact neg_ne_zero.mpr (h.1 1)
    · change det2 (a-b) (e-d) ≠ 0
      rw [det2_reverse_edge a b d e]
      exact neg_ne_zero.mpr (h.1 0)
  · intro i
    fin_cases i
    · exact h.2.1 0
    · exact h.2.1 2
    · exact h.2.1 1
  · intro i
    fin_cases i
    · change orient2 a c d ≠ 0 ∧ orient2 a c e ≠ 0
      rw [orient2_reverse_edge c a d,orient2_reverse_edge c a e]
      exact ⟨neg_ne_zero.mpr (h.2.2 2).1,neg_ne_zero.mpr (h.2.2 2).2⟩
    · change orient2 c b d ≠ 0 ∧ orient2 c b e ≠ 0
      rw [orient2_reverse_edge b c d,orient2_reverse_edge b c e]
      exact ⟨neg_ne_zero.mpr (h.2.2 1).1,neg_ne_zero.mpr (h.2.2 1).2⟩
    · change orient2 b a d ≠ 0 ∧ orient2 b a e ≠ 0
      rw [orient2_reverse_edge a b d,orient2_reverse_edge a b e]
      exact ⟨neg_ne_zero.mpr (h.2.2 0).1,neg_ne_zero.mpr (h.2.2 0).2⟩

theorem triangle_intersection_reverse (a b c d e : Plane) :
    triangleSegmentIntersection a c b d e = -triangleSegmentIntersection a b c d e := by
  unfold triangleSegmentIntersection
  rw [segmentCrossingSign_reverse_left c a d e,
    segmentCrossingSign_reverse_left b c d e,segmentCrossingSign_reverse_left a b d e]
  ring

def orientedTriangleIndicator (a b c z : Plane) : ℝ :=
  if 0 < orient2 a b c then triangleIndicator a b c z else -triangleIndicator a c b z

theorem oriented_triangle_entry_exit (a b c d e : Plane) (ha : orient2 a b c ≠ 0)
    (h : TriangleSegmentPosition a b c d e) :
    triangleSegmentIntersection a b c d e =
      orientedTriangleIndicator a b c e-orientedTriangleIndicator a b c d := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hac : 0 < orient2 a c b := by
      rw [triangle_area_cycle b a c,orient2_reverse_edge]
      exact neg_pos.mpr ha
    have hh := triangle_segment_entry_exit_of_position a c b d e hac (triangle_position_reverse a b c d e h)
    rw [triangle_intersection_reverse] at hh
    simp only [orientedTriangleIndicator,not_lt.mpr ha.le,ite_false]
    linarith
  · simpa only [orientedTriangleIndicator,ha,ite_true] using triangle_segment_entry_exit_of_position a b c d e ha h

theorem triangle_closed_walk_intersection_zero (a b c : Plane) (ha : orient2 a b c ≠ 0)
    (w : ℕ → Plane) (m : ℕ) (hw : w m = w 0)
    (h : ∀ j ∈ Finset.range m, TriangleSegmentPosition a b c (w j) (w (j+1))) :
    (∑ j ∈ Finset.range m, triangleSegmentIntersection a b c (w j) (w (j+1))) = 0 := by
  have hs := telescoping_real_sum (fun j => orientedTriangleIndicator a b c (w j)) m
  rw [hw,sub_self,Finset.sum_sub_distrib] at hs
  calc
    _ = ∑ j ∈ Finset.range m,
        (orientedTriangleIndicator a b c (w (j+1))-orientedTriangleIndicator a b c (w j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact oriented_triangle_entry_exit a b c _ _ ha (h j hj)
    _ = 0 := by rw [Finset.sum_sub_distrib]; linarith

end Zarankiewicz

end

end OAI
