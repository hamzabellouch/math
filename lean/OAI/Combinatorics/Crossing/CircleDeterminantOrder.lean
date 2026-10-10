import OAI.Combinatorics.Crossing.CircleChords
import OAI.Combinatorics.Crossing.PlanarDeterminant

namespace OAI

namespace Zarankiewicz

theorem circle_det_formula (a b : ℝ) :
    det2 (circlePoint a) (circlePoint b) =
      2*(b-a)*(1+a*b)/((1+a^2)*(1+b^2)) := by
  have ha := ne_of_gt (circle_denominator_pos a)
  have hb := ne_of_gt (circle_denominator_pos b)
  dsimp [det2,circlePoint]
  field_simp
  ring

theorem circle_det_pos_iff (a b : ℝ) (h : 0<1+a*b) :
    0<det2 (circlePoint a) (circlePoint b) ↔ a<b := by
  rw [circle_det_formula,div_pos_iff_of_pos_right (mul_pos (circle_denominator_pos a) (circle_denominator_pos b)),
    mul_pos_iff_of_pos_right h,mul_pos_iff_of_pos_left (show (0 : ℝ)<2 by norm_num),sub_pos]

theorem circle_det_neg_iff (a b : ℝ) (h : 0<1+a*b) :
    det2 (circlePoint a) (circlePoint b)<0 ↔ b<a := by
  have hh : 0<1+b*a := by nlinarith
  have he := circle_det_pos_iff b a hh
  rw [det2_swap,neg_pos] at he
  exact he

end Zarankiewicz

end OAI
