import OAI.Geometry.RCD.Harmonic.PointedRadialDistance

namespace OAI

/-! # Quantitative squared-distance errors for variational test recovery -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

theorem sq_error_of_abs_sub_le {a b B ε : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hbB : b≤B) (hε : 0≤ε) (he : |a-b|≤ε) :
    |a^2-b^2|≤ε*(2*B+ε) := by
  have hpm := abs_le.mp he
  rw [sq_sub_sq,abs_mul]
  have hab : 0≤a+b := add_nonneg ha hb
  rw [abs_of_nonneg hab]
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_right he hab).trans
    (mul_le_mul_of_nonneg_left (show a+b≤2*B+ε by linarith) hε)

theorem pointed_square_distance_error {X : Type*} [MetricSpace X]
    {n : ℕ} {p x y : X} {r S ε B : ℝ} {v : X → Euclidean n}
    (hr : 0<r) (hε : 0≤ε) (hv : IsPointedApproximation p 0 r S ε v)
    (hx : dist x p≤S*r) (hy : dist y p≤S*r) (hxy : dist x y/r≤B) :
    |dist (v x) (v y)^2-(dist x y/r)^2|≤ε*(2*B+ε) :=
  sq_error_of_abs_sub_le dist_nonneg (div_nonneg dist_nonneg hr.le) hxy hε
    (hv.2.1 x y hx hy)

theorem scaled_quadratic_cost {d t r : ℝ} (ht : 0<t) (hr : 0<r) :
    d^2/(2*(t*r^2))=(d/r)^2/(2*t) := by
  field_simp

end RegularPointCoordinates

end

end OAI
