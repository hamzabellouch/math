import OAI.Geometry.EinsteinFour.FourHeatGaussianEquation

namespace OAI

/-! Joint positive-time continuity of the Gaussian and its actual time derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Topology

noncomputable section

def fourHeatGaussianTimeFactor (t : ℝ) (x : FourSpace) : ℝ :=
  ‖x‖ ^ 2 / (4 * t ^ 2) - 2 / t

theorem fourHeatGaussian_joint_continuousOn :
    ContinuousOn (fun z : ℝ × FourSpace => fourHeatGaussian z.1 z.2) (Ioi 0 ×ˢ univ) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have ht : z.1 ≠ 0 := hz.1.ne'
  have hP : ContinuousAt (fun w : ℝ × FourSpace => ((4 * Real.pi * w.1) ^ 2)⁻¹) z :=
    ((continuousAt_const.mul continuousAt_fst).pow 2).inv₀
      (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht))
  have hE : ContinuousAt (fun w : ℝ × FourSpace => -(4 * w.1)⁻¹ * ‖w.2‖ ^ 2) z :=
    (((continuousAt_const.mul continuousAt_fst).inv₀ (mul_ne_zero (by norm_num) ht)).neg).mul
      (continuousAt_snd.norm.pow 2)
  exact hP.mul (Real.continuous_exp.continuousAt.comp hE)

theorem fourHeatGaussianTimeFactor_joint_continuousOn :
    ContinuousOn (fun z : ℝ × FourSpace => fourHeatGaussianTimeFactor z.1 z.2)
      (Ioi 0 ×ˢ univ) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have ht : z.1 ≠ 0 := hz.1.ne'
  exact ((continuousAt_snd.norm.pow 2).div
    (continuousAt_const.mul (continuousAt_fst.pow 2))
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht))).sub
    (continuousAt_const.div continuousAt_fst ht)

end
end PositiveEinsteinFour.Geometry

end OAI
