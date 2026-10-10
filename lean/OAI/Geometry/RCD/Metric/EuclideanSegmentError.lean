import OAI.Geometry.RCD.Coordinates.QuadraticMetricError

namespace OAI

/-! # Quantitative Euclidean interpolation from three squared distances -/

open Metric
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_segment_square {n : ℕ} (x y z : Euclidean n) (t : ℝ) :
    dist z ((1-t) • x+t • y)^2=
      (1-t)*dist z x^2+t*dist z y^2-t*(1-t)*dist x y^2 := by
  simp only [dist_eq_norm,← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm y x,real_inner_comm z x,real_inner_comm z y]
  ring

theorem euclidean_segment_error {n : ℕ} (x y z : Euclidean n) {t d E : ℝ}
    (ht : 0≤t) (ht1 : t≤1) (hE : 0≤E)
    (hx : |dist z x^2-(t*d)^2|≤E)
    (hy : |dist z y^2-((1-t)*d)^2|≤E)
    (hxy : |dist x y^2-d^2|≤E) :
    dist z ((1-t) • x+t • y)≤Real.sqrt (2*E) := by
  have hx' := mul_le_mul_of_nonneg_left (abs_le.mp hx).2 (sub_nonneg.mpr ht1)
  have hy' := mul_le_mul_of_nonneg_left (abs_le.mp hy).2 ht
  have hxy' := mul_le_mul_of_nonneg_left (abs_le.mp hxy).1
    (mul_nonneg ht (sub_nonneg.mpr ht1))
  have hcoef : t*(1-t)≤1 :=
    (mul_le_mul_of_nonneg_left (show 1-t≤1 by linarith) ht).trans (by simpa using ht1)
  have hbound : dist z ((1-t) • x+t • y)^2≤2*E := by
    rw [euclidean_segment_square]
    have hid : (1-t)*(t*d)^2+t*((1-t)*d)^2-t*(1-t)*d^2=0 := by ring
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hcoef)]
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hE)
  nlinarith [dist_nonneg (x := z) (y := (1-t) • x+t • y),Real.sqrt_nonneg (2*E)]

end RegularPointCoordinates

end

end OAI
