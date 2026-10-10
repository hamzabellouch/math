import OAI.Combinatorics.Crossing.SegmentSides

namespace OAI

noncomputable section
namespace Zarankiewicz

def circlePoint (t : ℝ) : Plane := ((1-t^2)/(1+t^2), 2*t/(1+t^2))

theorem circle_denominator_pos (t : ℝ) : 0 < 1+t^2 := by nlinarith [sq_nonneg t]

theorem circlePoint_on_unit_circle (t : ℝ) : (circlePoint t).1^2+(circlePoint t).2^2 = 1 := by
  have h := ne_of_gt (circle_denominator_pos t)
  dsimp [circlePoint]
  field_simp
  ring

theorem circlePoint_parameter (t : ℝ) : (circlePoint t).2/(1+(circlePoint t).1) = t := by
  have h := ne_of_gt (circle_denominator_pos t)
  have hden : 1+(circlePoint t).1 = 2/(1+t^2) := by
    dsimp [circlePoint]
    field_simp
    ring
  rw [hden]
  dsimp [circlePoint]
  field_simp

theorem circlePoint_injective : Function.Injective circlePoint := by
  intro a b hab
  have hh := congrArg (fun z : Plane => z.2/(1+z.1)) hab
  simpa only [circlePoint_parameter] using hh

theorem circle_orient_formula (a b c : ℝ) :
    orient2 (circlePoint a) (circlePoint b) (circlePoint c) =
      4*(b-a)*(c-a)*(c-b)/((1+a^2)*(1+b^2)*(1+c^2)) := by
  have ha := ne_of_gt (circle_denominator_pos a)
  have hb := ne_of_gt (circle_denominator_pos b)
  have hc := ne_of_gt (circle_denominator_pos c)
  dsimp [orient2,det2,circlePoint]
  field_simp
  ring

theorem circle_orient_pos (a b c : ℝ) (hab : a<b) (hbc : b<c) :
    0 < orient2 (circlePoint a) (circlePoint b) (circlePoint c) := by
  rw [circle_orient_formula]
  exact div_pos
    (mul_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hab))
      (sub_pos.mpr (hab.trans hbc))) (sub_pos.mpr hbc))
    (mul_pos (mul_pos (circle_denominator_pos a) (circle_denominator_pos b)) (circle_denominator_pos c))

theorem orient2_cycle (a b c : Plane) : orient2 b c a = orient2 a b c := by
  dsimp [orient2,det2]
  ring

theorem orient2_swap_ends (a b c : Plane) : orient2 a c b = -orient2 a b c := by
  exact det2_swap (b-a) (c-a)

theorem circle_chords_alternating_positive (a c b d : ℝ) (hac : a<c) (hcb : c<b) (hbd : b<d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) = 1 := by
  apply segmentCrossingSign_of_positive_sides
  · rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos a c b hac hcb)
  · exact circle_orient_pos a b d (hac.trans hcb) hbd
  · rw [orient2_cycle]
    exact circle_orient_pos a c d hac (hcb.trans hbd)
  · rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos c b d hcb hbd)

end Zarankiewicz

end

end OAI
