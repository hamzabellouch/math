import OAI.NumberTheory.JointDickman.Amplification.EndpointParameterVariation

namespace OAI

/-! # The normalized reciprocal lag is uniformly Lipschitz away from zero -/
namespace JointDickman

theorem reciprocal_lag_difference {T η x y : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hx : η*T ≤ x) (hy : η*T ≤ y) :
    |T/x-T/y| ≤ |x-y|/(η^2*T) := by
  have hx0 : 0 < x := (mul_pos hη hT).trans_le hx
  have hy0 : 0 < y := (mul_pos hη hT).trans_le hy
  have hxy : η^2*T^2 ≤ x*y := by
    have hh := mul_le_mul hx hy (mul_pos hη hT).le hx0.le
    nlinarith
  have he : T/x-T/y = T*(y-x)/(x*y) := by field_simp
  rw [he,abs_div,abs_mul,abs_of_pos hT,abs_of_pos (mul_pos hx0 hy0),abs_sub_comm y x]
  have hb := div_le_div_of_nonneg_left (mul_nonneg hT.le (abs_nonneg (x-y)))
    (by positivity : 0 < η^2*T^2) hxy
  refine hb.trans_eq ?_
  field_simp

end JointDickman

end OAI
