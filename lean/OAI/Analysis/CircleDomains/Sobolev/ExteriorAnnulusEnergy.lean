import OAI.Analysis.CircleDomains.Sobolev.ExteriorAngularEnergy
import OAI.Analysis.CircleDomains.Sobolev.PolarAnnulusIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-! A principal holomorphic exterior map pays at least the Euclidean
area of each source annulus in squared derivative energy. -/
open Set Filter Function Metric Asymptotics Bornology Real MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma polar_constant_annulus_energy {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ r in Ioo a b, ENNReal.ofReal r * ENNReal.ofReal (2*Real.pi)) =
      ENNReal.ofReal (Real.pi*(b^2-a^2)) := by
  have hi : IntegrableOn (fun r : ℝ => r*(2*Real.pi)) (Ioo a b) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
      ((continuous_id.mul continuous_const).intervalIntegrable _ _)
  have he : (∫ r in Ioo a b, r*(2*Real.pi)) = Real.pi*(b^2-a^2) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_mul_const, integral_id]
    ring
  calc
    _ = ∫⁻ r in Ioo a b, ENNReal.ofReal (r*(2*Real.pi)) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      change ENNReal.ofReal r * ENNReal.ofReal (2*Real.pi) = ENNReal.ofReal (r*(2*Real.pi))
      rw [ENNReal.ofReal_mul (ha.trans hr.1.le)]
    _ = ENNReal.ofReal (∫ r in Ioo a b, r*(2*Real.pi)) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hi
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact mul_nonneg (ha.trans hr.1.le) (by positivity)
    _ = _ := by rw [he]

lemma exterior_annulus_energy {F : ℂ → ℂ} {R a b : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0))
    (ha : R < a) (hab : a ≤ b) :
    ENNReal.ofReal (Real.pi*(b^2-a^2)) ≤
      ∫⁻ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, ENNReal.ofReal (‖deriv F z‖^2) := by
  have hap : 0 ≤ a := (hR.trans ha).le
  rw [lintegral_circleMap_annulus _ ((measurable_deriv F).norm.pow_const 2).ennreal_ofReal hap,
    ← polar_constant_annulus_energy hap hab]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  gcongr
  exact exterior_derivative_angular_energy hR hF ht (ha.trans hr.1)

end CircleDomainRigidity

end

end OAI
