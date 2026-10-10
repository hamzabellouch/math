import OAI.Geometry.RCD.Transport.ExponentialEntropyComparison
import OAI.Geometry.RCD.Transport.RelativeEntropyDerivative

namespace OAI

/-! # Boltzmann entropy differentiates along the actual exponential heat variation -/

open Set Filter MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heat_exponential_entropy_hasDerivAt_zero (r : Lp ℝ 2 μ) (hr : 0≤r)
    (hri : Integrable r μ) {g : X → ℝ} (hg : Measurable g)
    {M : ℝ≥0} (hgb : ∀ x, |g x|≤M) (s : ℝ)
    (he : Integrable (fun x => heatAt μ hQ s r x*Real.log (heatAt μ hQ s r x)) μ) :
    HasDerivAt (fun t : ℝ => ∫ x, heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) x*
      Real.log (heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) x) ∂μ)
      (∫ x, (1+Real.log (heatAt μ hQ s r x))*
        heatAt μ hQ s (lpMultiplier μ (boundedMultiplier μ g hg M hgb) r) x ∂μ) 0 := by
  apply relative_entropy_integral_hasDerivAt_zero μ
    (B:=M) (C:=M^2) (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
    ((Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ s r hr))
    (fun t => (Lp.coeFn_nonneg _).mpr (heat_exponential_nonneg μ hQ r hr hg hgb s t))
    (by rw [exponentialTiltLp_zero]) (heatAt_integrable μ hQ s r hri) he
    (fun t => heat_exponential_entropy_integrable μ hQ r hr hg hgb s t
      (heatAt_integrable μ hQ s r hri) he)
    (heat_exponential_tangent_bound μ hQ r hr hg hgb s)
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| * M≤1 := by
    have hc : Continuous (fun t : ℝ => |t| * (M:ℝ)) := continuous_abs.mul continuous_const
    filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds (by simp : |(0:ℝ)| * (M:ℝ)<1))] with t ht
    exact ht.le
  filter_upwards [hnear] with t ht
  exact heat_exponential_remainder_bound μ hQ r hr hg hgb s ht

end RegularPointCoordinates

end

end OAI
