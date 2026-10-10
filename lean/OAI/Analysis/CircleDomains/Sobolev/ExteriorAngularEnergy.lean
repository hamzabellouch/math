import OAI.Analysis.CircleDomains.Sobolev.ExteriorCircleEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! The exact angular-energy lower bound in the nonnegative integral
used by polar change of variables. -/
open Set Filter Function Metric Asymptotics Bornology Real MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exterior_derivative_angular_energy {F : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) (hr : R < r) :
    ENNReal.ofReal (2*Real.pi) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (‖deriv F (circleMap 0 r θ)‖^2) := by
  have hrp : 0 < r := hR.trans hr
  let g : ℝ → ℝ := fun θ => ‖deriv F (circleMap 0 r θ)‖^2
  have hc : Continuous g := by
    apply (exterior_derivative_continuousOn_circle hF hr).norm.pow 2 |>.comp_continuous
      (continuous_circleMap 0 r)
    intro θ
    simpa only [abs_of_pos hrp] using circleMap_mem_sphere' (0 : ℂ) r θ
  have hi : IntegrableOn g (Ioo (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])).mp
      (hc.intervalIntegrable _ _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun θ => sq_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  have he : (∫ θ in Ioo (-Real.pi) Real.pi, g θ) = ∫ θ in (0 : ℝ)..2*Real.pi, g θ := by
    have hp : Periodic g (2*Real.pi) := by
      intro θ
      dsimp only [g]
      rw [periodic_circleMap 0 r θ]
    have hs := hp.intervalIntegral_add_eq (-Real.pi) 0
    have ha : -Real.pi+2*Real.pi = Real.pi := by ring
    rw [ha, zero_add, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo] at hs
    exact hs
  rw [he]
  have hav := exterior_derivative_circle_energy hR hF ht hr
  change 1 ≤ (2*Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2*Real.pi, g θ) at hav
  simpa only [mul_one] using (le_inv_mul_iff₀ (by positivity : 0 < 2*Real.pi)).mp hav

end CircleDomainRigidity

end

end OAI
