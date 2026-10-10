import OAI.Geometry.RCD.Sobolev.MeasuredRadialCutoff

namespace OAI

/-! # Both radial cutoff representatives vanish outside one interior ball -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem measured_radial_cutoff_zero_outside {n : ℕ} {p : X} {r S ε a b R : ℝ}
    (hr : 0<r) (hS : 0≤S) (hab : a<b) (hsmall : 2*ε<R-b)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {x : X} (hx : dist x p≤S*r) (hnot : x∉ball p (R*r)) :
    nestedBallCutoff p (a*r) (b*r) x=0 ∧ euclideanNestedCutoff n hab (v x)=0 := by
  have hd := abs_le.mp (pointed_radial_distance hr hS hv hx)
  have hR : R*r≤dist x p := le_of_not_gt hnot
  have hR' : R≤dist x p/r := (le_div_iff₀ hr).mpr hR
  have hb : b<‖v x‖ := by linarith
  have hε : 0≤ε := le_trans dist_nonneg hv.1
  have hbR : b<R := by linarith
  constructor
  · apply nestedBallCutoff_eq_zero p (mul_lt_mul_of_pos_right hab hr)
    rw [dist_comm p x]
    exact (mul_le_mul_of_nonneg_right hbR.le hr.le).trans hR
  · exact nestedBallCutoff_eq_zero 0 hab (by simpa only [dist_zero_left] using hb.le)

end RegularPointCoordinates

end

end OAI
