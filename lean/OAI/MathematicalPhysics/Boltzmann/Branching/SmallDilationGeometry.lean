import OAI.MathematicalPhysics.Boltzmann.Approximation.DormantConstruction
import OAI.MathematicalPhysics.Boltzmann.Branching.HotSeedCoreLower

namespace OAI

/-! # Uniform geometry of small dilations on bounded sets -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem norm_quarter_mem_cube {x : Velocity} (hx : ‖x‖ ≤ 1/4) : x ∈ TorusChart.cube := by
  intro i
  have hi : |x i| ≤ 1/4 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hx
  exact ⟨by linarith [(abs_le.mp hi).1],by linarith [(abs_le.mp hi).2]⟩

theorem eventually_dilation_in_window {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hlim : Tendsto r atTop (𝓝 0)) {T : ℝ} (hT : 0 < T) (B R : ℝ) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) B, ∀ x : Velocity, ‖x‖ ≤ R →
      r n*t ∈ Icc 0 T ∧ r n • x ∈ TorusChart.cube := by
  have htl : Tendsto (fun n => r n*B) atTop (𝓝 0) := by simpa only [zero_mul] using hlim.mul_const B
  have hxl : Tendsto (fun n => r n*R) atTop (𝓝 0) := by simpa only [zero_mul] using hlim.mul_const R
  have ht := htl.eventually (gt_mem_nhds hT)
  have hx := hxl.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4))
  filter_upwards [ht,hx] with n hn hn' t ht x hxn
  constructor
  · exact ⟨mul_nonneg (hr n).le ht.1,
      (mul_le_mul_of_nonneg_left ht.2 (hr n).le).trans hn.le⟩
  · apply norm_quarter_mem_cube
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hr n)]
    exact (mul_le_mul_of_nonneg_left hxn (hr n).le).trans hn'.le

theorem H_le_off_axis {q ε : ℝ} (hq : 0 ≤ q) (hε : 0 < ε) {v : Velocity}
    (hv : ε ≤ ‖transverse v‖) : H q v ≤ 1+ε^(-q) := by
  have he : Real.exp (-‖v‖^2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have hp : (1+‖v‖^2)^(-50 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖v‖]) (by norm_num)
  have hr : ‖transverse v‖^(-q) ≤ ε^(-q) :=
    Real.rpow_le_rpow_of_nonpos hε hv (neg_nonpos.mpr hq)
  unfold H singularity
  have hm : Real.exp (-‖v‖^2)*(1+‖v‖^2)^(-50 : ℝ) ≤ 1 := by
    simpa using mul_le_mul he hp (Real.rpow_nonneg (by positivity) _) (by norm_num : (0:ℝ) ≤ 1)
  exact (mul_le_mul_of_nonneg_right hm (by positivity)).trans (by linarith)

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
