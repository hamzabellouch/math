import OAI.Probability.SLE.Loewner.SlitUniformForwardBound
import OAI.Probability.SLE.Loewner.InitialChartIdentities

namespace OAI

/-! A common radius for the physical slit gives a common bound on all
inverse charts above a bounded coordinate set. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.exterior_displacement_le_radius {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    {z : ℂ} (hzH : z∈upperHalfPlane) (hz : 2*R≤‖z‖) :
    ‖P.forward z-z‖≤3*R := by
  have hn : 0<‖z‖ := lt_of_lt_of_le (by linarith : 0<2*R) hz
  have hb := P.forward_kernel_remainder hi h0 hH hR hp hzH hz
  have hc := P.capacity_le_radius_sq hR (fun t => (hp t).le)
  have hquad : 4*R^2≤‖z‖^2 := by nlinarith
  have hfirst : 10*P.capacity*R/‖z‖^2≤5*R/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hR.le,
      mul_le_mul_of_nonneg_left hquad hR.le]
  have hsecond : P.capacity/‖z‖≤R/2 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith [mul_le_mul_of_nonneg_left hz hR.le]
  have hdiv : ‖(P.capacity:ℂ)/z‖=P.capacity/‖z‖ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos P.capacity_pos]
  have htri := norm_sub_le_norm_sub_add_norm_sub (P.forward z-z) ((P.capacity:ℂ)/z) 0
  simp only [sub_zero] at htri
  rw [hdiv] at htri
  linarith

theorem SimpleSlitChart.inverse_uniform_bound {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    {w : ℂ} (hw : w∈upperHalfPlane) : ‖P.inverse w‖≤‖w‖+3*R := by
  by_cases hz : ‖P.inverse w‖≤2*R
  · linarith [norm_nonneg w]
  have hb := P.exterior_displacement_le_radius hi h0 hH hR hp (P.inverse_mapsTo hw).1
    (le_of_not_ge hz)
  rw [P.right_inverse w hw] at hb
  have ht := norm_le_norm_sub_add (P.inverse w) w
  rw [norm_sub_rev] at hb
  linarith

theorem initialInverse_uniform_bound (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    (s : unitInterval) {w : ℂ} (hw : w∈upperHalfPlane) :
    ‖initialInverseChart p hi h0 hH s w‖≤‖w‖+3*R := by
  by_cases hs : s=0
  · subst s
    rw [initialInverseChart_zero]
    change ‖w‖≤‖w‖+3*R
    linarith
  · rw [initialInverseChart,dite_eq_right hs]
    exact (initialSlitChart p hi h0 hH s hs).inverse_uniform_bound
      (initialSubarc_injective hi hs) (by simpa only [initialSubarc_zero] using h0)
      (initialSubarc_upper hH hs) hR (fun u => hp _) hw

end SLEExactGauge

end

end OAI
