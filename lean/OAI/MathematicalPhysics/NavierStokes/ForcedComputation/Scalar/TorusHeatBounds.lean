import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatInput
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.HeatGaussianBounds

namespace OAI

/-! Two numerical heat bounds derived from the flat-torus Gaussian estimate. -/

noncomputable section
namespace ForcedComputation.VelocityDetector

theorem torusHeatKernel_after_one (hK : TorusHeatInput) {t : ℝ} (ht : 1 ≤ t)
    (x : ShearFlows.Plane) : torusHeatKernel t x ≤ 16 := by
  have ht₀ : 0 < t := by linarith
  have hπ := Real.pi_gt_three
  have hq : 1 / (4 * Real.pi * t) ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    nlinarith
  have hs : Real.sqrt (1 / (4 * Real.pi * t)) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  have he : Real.exp (-(torusDistanceSq x) / (4 * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (torusDistanceSq_nonneg x))
      (by positivity)
  calc
    torusHeatKernel t x ≤
        4 * (1 + Real.sqrt (1 / (4 * Real.pi * t))) ^ 2 *
          Real.exp (-(torusDistanceSq x) / (4 * t)) := hK.gaussian t ht₀ x
    _ ≤ 4 * (1 + Real.sqrt (1 / (4 * Real.pi * t))) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ 16 := by nlinarith [Real.sqrt_nonneg (1 / (4 * Real.pi * t))]

theorem torusHeatKernel_separated (hK : TorusHeatInput) {t d : ℝ}
    (ht : 0 < t) (hd : 0 < d) (x : ShearFlows.Plane)
    (hx : d ^ 2 ≤ torusDistanceSq x) : torusHeatKernel t x ≤ 8 + 64 / d ^ 2 := by
  have hπ := Real.pi_gt_three
  have hq : 1 / (4 * Real.pi * t) ≤ t⁻¹ := by
    rw [one_div, inv_le_inv₀ (by positivity) ht]
    nlinarith
  have hs : Real.sqrt (1 / (4 * Real.pi * t)) ^ 2 = 1 / (4 * Real.pi * t) :=
    Real.sq_sqrt (by positivity)
  have hc : 4 * (1 + Real.sqrt (1 / (4 * Real.pi * t))) ^ 2 ≤ 8 + 8 * t⁻¹ := by
    nlinarith [sq_nonneg (Real.sqrt (1 / (4 * Real.pi * t)) - 1)]
  have hdist : d ^ 2 / (8 * t) ≤ torusDistanceSq x / (4 * t) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg d]
  have he : Real.exp (-(torusDistanceSq x) / (4 * t)) ≤
      Real.exp (-(d ^ 2 / (8 * t))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    exact neg_le_neg hdist
  have he₁ : Real.exp (-(d ^ 2 / (8 * t))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  calc
    torusHeatKernel t x ≤
        4 * (1 + Real.sqrt (1 / (4 * Real.pi * t))) ^ 2 *
          Real.exp (-(torusDistanceSq x) / (4 * t)) := hK.gaussian t ht x
    _ ≤ 4 * (1 + Real.sqrt (1 / (4 * Real.pi * t))) ^ 2 *
          Real.exp (-(d ^ 2 / (8 * t))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ (8 + 8 * t⁻¹) * Real.exp (-(d ^ 2 / (8 * t))) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = 8 * Real.exp (-(d ^ 2 / (8 * t))) +
        8 * (t⁻¹ * Real.exp (-(d ^ 2 / (8 * t)))) := by ring
    _ ≤ 8 * 1 + 8 * (8 / d ^ 2) := add_le_add
      (mul_le_mul_of_nonneg_left he₁ (by norm_num))
      (mul_le_mul_of_nonneg_left (gaussian_time_factor hd ht) (by norm_num))
    _ = 8 + 64 / d ^ 2 := by ring

theorem torusHeatKernel_detector_bounds (hK : TorusHeatInput) {t : ℝ} (ht : 0 < t)
    (x : ShearFlows.Plane) :
    (1 ≤ t ∨ (1 / 32 : ℝ) ^ 2 ≤ torusDistanceSq x → torusHeatKernel t x < 1000000000) ∧
    (1 ≤ t ∨ (1 / 16 : ℝ) ^ 2 ≤ torusDistanceSq x → torusHeatKernel t x < 100000000) := by
  constructor
  · intro h
    rcases h with h | h
    · exact (torusHeatKernel_after_one hK h x).trans_lt (by norm_num)
    · exact (torusHeatKernel_separated hK ht (by norm_num : (0 : ℝ) < 1 / 32) x h).trans_lt
        (by norm_num)
  · intro h
    rcases h with h | h
    · exact (torusHeatKernel_after_one hK h x).trans_lt (by norm_num)
    · exact (torusHeatKernel_separated hK ht (by norm_num : (0 : ℝ) < 1 / 16) x h).trans_lt
        (by norm_num)

end ForcedComputation.VelocityDetector

end

end OAI
