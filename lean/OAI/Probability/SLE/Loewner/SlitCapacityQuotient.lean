import OAI.Probability.SLE.Loewner.SlitCapacityRemainder

namespace OAI

/-! Dividing by the positive, exact capacity gives the first-order
Loewner kernel with a radius-controlled error. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

theorem SimpleSlitChart.forward_quotient_kernel {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    {z : ℂ} (hzH : z∈upperHalfPlane) (hz : 2*R≤‖z‖) :
    ‖(P.forward z-z)/(P.capacity:ℂ)-1/z‖≤10*R/‖z‖^2 := by
  have hc : (P.capacity:ℂ)≠0 := ofReal_ne_zero.mpr P.capacity_pos.ne'
  have he : (P.forward z-z)/(P.capacity:ℂ)-1/z=
      (P.forward z-z-(P.capacity:ℂ)/z)/(P.capacity:ℂ) := by
    field_simp [hc]
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos P.capacity_pos]
  have hb := div_le_div_of_nonneg_right
    (P.forward_kernel_remainder hi h0 hH hR hp hzH hz) P.capacity_pos.le
  apply hb.trans_eq
  field_simp [P.capacity_pos.ne']

end SLEExactGauge

end

end OAI
