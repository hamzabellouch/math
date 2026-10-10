import OAI.Geometry.RCD.Sobolev.EndpointLIntegralLimit
import OAI.Geometry.RCD.Transport.BoundedPathDistortion

namespace OAI

/-! # Weak limits of the actual inverse-density distortion integrals -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem weak_inverse_density_distortion
    (μ ν : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν] [ν.WeaklyRegular]
    (hν : ν ≪ μ)
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (π : ProbabilityMeasure C(Time,X))
    (hlim : Tendsto πs atTop (𝓝 π)) (u : Time)
    (hds : ∀ j, (πs j : Measure C(Time,X)).map (fun γ => γ u) ≤ (2 : ℝ≥0∞) • ν)
    (hd : (π : Measure C(Time,X)).map (fun γ => γ u) ≤ (2 : ℝ≥0∞) • ν)
    {K N s : ℝ} (hK : K ≤ 0) (hN : 0 < N) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hi : Integrable (fun x => (ν.rnDeriv μ x).toReal^(-(1/N))) ν) :
    Tendsto (fun j => ∫⁻γ,sigma K (N+1) s (dist (γ 0) (γ 1))*
        (ν.rnDeriv μ (γ u))^(-(1/N)) ∂(πs j : Measure C(Time,X))) atTop
      (𝓝 (∫⁻γ,sigma K (N+1) s (dist (γ 0) (γ 1))*
        (ν.rnDeriv μ (γ u))^(-(1/N)) ∂(π : Measure C(Time,X)))) := by
  let φ := pathDistortion (X:=X) K (N+1) s hK (by linarith) hs hs1
  have hφ (γ) : 0 ≤ φ γ := ENNReal.toReal_nonneg
  have he (γ : C(Time,X)) : ENNReal.ofReal (φ γ)=sigma K (N+1) s (dist (γ 0) (γ 1)) :=
    ENNReal.ofReal_toReal (sigma_nonpos_ne_top (t:=s) hK (by linarith) dist_nonneg)
  have hf : ∀ᵐ x ∂ν, (ν.rnDeriv μ x)^(-(1/N)) ≠ ∞ := by
    filter_upwards [Measure.rnDeriv_pos hν,hν.ae_le (Measure.rnDeriv_lt_top ν μ)] with x hx ht
    exact ENNReal.rpow_ne_top_of_ne_zero hx.ne' ht.ne
  have hi' : Integrable (fun x => ((ν.rnDeriv μ x)^(-(1/N))).toReal) ν := by
    simpa only [←ENNReal.toReal_rpow] using hi
  have hh := weak_endpoint_weight_lintegral ν πs π hlim u hds hd φ hφ hf hi'
  simpa only [he] using hh

end RegularPointCoordinates

end

end OAI
