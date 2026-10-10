import OAI.Geometry.CylinderCovering.Rational.CeilingIntegralDefinitions
import OAI.Geometry.CylinderCovering.Rational.Integrals

namespace OAI

open Filter
open scoped Topology

noncomputable section
namespace SlopeRational

theorem ceilingIntegral_eq (d : ℝ) :
    ceilingIntegral d = alpha d * (ceilingConstant d / 96 + ceilingQuadratic d / 2560) := by
  exact CylinderCovering.RationalIntegrals.ceiling_integral _ _ _

theorem ceilingIntegral_formula (d : ℝ) :
    ceilingIntegral d = (2 + 5 * d) / (1920 * (1 + 2 * d) ^ 3) := by
  rw [ceilingIntegral_eq]
  exact CylinderCovering.RationalIntegrals.rational_ceiling_coefficient_formula d

theorem ceilingIntegral_tendsto_zero :
    Tendsto ceilingIntegral (𝓝 0) (𝓝 (1 / 960 : ℝ)) := by
  exact CylinderCovering.RationalIntegrals.rational_ceiling_integral_tendsto

theorem ceilingIntegral_tendsto_zero_right :
    Tendsto ceilingIntegral (𝓝[Set.Ioi 0] 0) (𝓝 (16 / 15360 : ℝ)) := by
  have h : Tendsto ceilingIntegral (𝓝[Set.Ioi 0] 0) (𝓝 (1 / 960 : ℝ)) :=
    ceilingIntegral_tendsto_zero.mono_left nhdsWithin_le_nhds
  norm_num at h ⊢
  exact h

theorem ceilingIntegral_pos {d : ℝ} (hd : 0 ≤ d) : 0 < ceilingIntegral d := by
  rw [ceilingIntegral_formula]
  positivity

end SlopeRational

end

end OAI
