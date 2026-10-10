import OAI.Probability.ContinuumTransition.FreeLimit

namespace OAI

section
open scoped Topology BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem hasCompactSupport_kernel : HasCompactSupport kernel := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1)
  intro x hx
  have hx' : ¬ ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  exact kernel_zero_outside (lt_of_not_ge hx').le

theorem exists_lipschitz_kernel : ∃ C : NNReal, LipschitzWith C kernel :=
  ContDiff.lipschitzWith_of_hasCompactSupport hasCompactSupport_kernel contDiff_kernel (by simp)

noncomputable def scaledKernel (R : ℝ) (x : Space) : ℝ := scaledKernelProfile R ‖x‖

theorem scaledKernel_eq {R : ℝ} (hR : 0 < R) (x : Space) :
    scaledKernel R x = R⁻¹^3*kernel (R⁻¹ • x) := by
  simp only [scaledKernel, scaledKernelProfile, kernel, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR), div_eq_mul_inv, mul_comm R⁻¹ ‖x‖]

theorem scaledKernel_nonneg {R : ℝ} (hR : 0 < R) (x : Space) : 0 ≤ scaledKernel R x :=
  scaledKernelProfile_nonneg hR ‖x‖

theorem scaledKernel_zero {R : ℝ} (hR : 0 < R) {x : Space} (hx : R ≤ ‖x‖) :
    scaledKernel R x = 0 := scaledKernelProfile_zero hR hx

theorem scaledKernel_neg (R : ℝ) (x : Space) : scaledKernel R (-x) = scaledKernel R x := by
  simp only [scaledKernel, norm_neg]

theorem integrable_scaledKernel {R : ℝ} (hR : 0 < R) : Integrable (scaledKernel R) := by
  change Integrable (fun x => scaledKernel R x)
  simp_rw [scaledKernel_eq hR]
  exact ((integrable_comp_smul_iff volume kernel (inv_ne_zero hR.ne')).2
    (contDiff_kernel.continuous.integrable_of_hasCompactSupport hasCompactSupport_kernel)).const_mul _

theorem integral_scaledKernel {R : ℝ} (hR : 0 < R) : ∫ x, scaledKernel R x = 1 := by
  simp_rw [scaledKernel_eq hR]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume kernel hR.le,
    integral_kernel]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, mul_one]
  field_simp

theorem scaledKernel_oscillation {C : NNReal} (hC : LipschitzWith C kernel)
    {R : ℝ} (hR : 0 < R) (x y : Space) :
    |scaledKernel R x-scaledKernel R y| ≤ (C : ℝ)/R^4*‖x-y‖ := by
  have hh := hC.norm_sub_le (R⁻¹ • x) (R⁻¹ • y)
  rw [← smul_sub, norm_smul] at hh
  simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)] at hh
  simp_rw [scaledKernel_eq hR]
  rw [← mul_sub, abs_mul, abs_of_pos (pow_pos (inv_pos.mpr hR) 3)]
  have hm := mul_le_mul_of_nonneg_left hh (pow_pos (inv_pos.mpr hR) 3).le
  convert hm using 1; try rfl
  field_simp

end ContinuumTemperature
end

end OAI
