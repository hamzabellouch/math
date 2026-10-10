import OAI.Geometry.RCD.Heat.HeatBridgeSecondDerivative

namespace OAI

/-! # Physical-time scaling of the exact heat-bridge second derivative

The heat time is lambda times the interpolation time, so the second
variation retains the exact lambda-squared coefficient.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ Q ker)

theorem kernelHeat_scaled_bridge_second_hasDerivAt (θ : Lp ℝ ∞ μ) (f g : Lp ℝ 2 μ)
    {τ t : ℝ} (hτ : 0 < τ) (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (deriv (fun s => ∫ x, θ x*(kernelHeat μ Q hk (τ*s) f x*
      kernelHeat μ Q hk (τ-τ*s) g x) ∂μ))
      (τ^2*heatBridgeSecondVariation μ Q θ f g τ (τ*t)) t := by
  have hlt : τ*t<τ := by nlinarith
  have hd := (heatBridgeVariation_hasDerivAt μ Q θ f g (mul_pos hτ ht) hlt).scomp t
    ((hasDerivAt_id t).const_mul τ)
  have hd' : HasDerivAt (fun s => τ*heatBridgeVariation μ Q θ f g τ (τ*s))
      (τ^2*heatBridgeSecondVariation μ Q θ f g τ (τ*t)) t := by
    convert hd.const_mul τ using 1 <;> simp only [Function.comp_def,smul_eq_mul]
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht ht1] with s hs
  have hls : τ*s<τ := by nlinarith [hs.2]
  have he := (kernelHeat_bridge_pairing_hasDerivAt_variation μ Q hk θ f g
    (mul_pos hτ hs.1) hls).scomp s ((hasDerivAt_id s).const_mul τ)
  simpa only [Function.comp_def,id_eq,smul_eq_mul,mul_one] using he.deriv

end RegularPointCoordinates

end

end OAI
