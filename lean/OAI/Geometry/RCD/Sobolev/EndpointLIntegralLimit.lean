import OAI.Geometry.RCD.Sobolev.WeakEndpointWeights

namespace OAI

/-! # Nonnegative endpoint-weighted integrals under weak convergence -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem endpoint_weight_lintegral_eq
    (ν : Measure X) (π : Measure C(Time,X)) (t : Time)
    (hd : π.map (fun γ => γ t) ≤ (2 : ℝ≥0∞) • ν)
    (φ : C(Time,X) →ᵇ ℝ) (hφ : ∀ γ, 0 ≤ φ γ)
    {f : X → ℝ≥0∞} (hf : ∀ᵐ x ∂ν, f x ≠ ∞)
    (hi : Integrable (fun x => (f x).toReal) ν) :
    (∫⁻γ,ENNReal.ofReal (φ γ)*f (γ t) ∂π)=
      ENNReal.ofReal (∫γ,φ γ*(f (γ t)).toReal ∂π) := by
  have hif := integrable_endpoint_of_domination π ν t hd hi
  have hib := hif.bdd_mul φ.continuous.measurable.aestronglyMeasurable
    (Eventually.of_forall φ.norm_coe_le_norm)
  rw [ofReal_integral_eq_lintegral_ofReal hib
    (Eventually.of_forall fun γ => mul_nonneg (hφ γ) ENNReal.toReal_nonneg)]
  apply lintegral_congr_ae
  have hm : ∀ᵐ x ∂π.map (fun γ => γ t), f x ≠ ∞ :=
    hd.absolutelyContinuous.ae_le ((Measure.smul_absolutelyContinuous).ae_le hf)
  filter_upwards [ae_of_ae_map (measurable_path_eval t).aemeasurable hm] with γ hγ
  rw [ENNReal.ofReal_mul (hφ γ),ENNReal.ofReal_toReal hγ]

theorem weak_endpoint_weight_lintegral
    (ν : Measure X) [IsFiniteMeasure ν] [ν.WeaklyRegular]
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (π : ProbabilityMeasure C(Time,X))
    (hlim : Tendsto πs atTop (𝓝 π)) (t : Time)
    (hds : ∀ j, (πs j : Measure C(Time,X)).map (fun γ => γ t) ≤ (2 : ℝ≥0∞) • ν)
    (hd : (π : Measure C(Time,X)).map (fun γ => γ t) ≤ (2 : ℝ≥0∞) • ν)
    (φ : C(Time,X) →ᵇ ℝ) (hφ : ∀ γ, 0 ≤ φ γ)
    {f : X → ℝ≥0∞} (hf : ∀ᵐ x ∂ν, f x ≠ ∞)
    (hi : Integrable (fun x => (f x).toReal) ν) :
    Tendsto (fun j => ∫⁻γ,ENNReal.ofReal (φ γ)*f (γ t) ∂(πs j : Measure C(Time,X))) atTop
      (𝓝 (∫⁻γ,ENNReal.ofReal (φ γ)*f (γ t) ∂(π : Measure C(Time,X)))) := by
  simp_rw [endpoint_weight_lintegral_eq ν _ t (hds _) φ hφ hf hi,
    endpoint_weight_lintegral_eq ν _ t hd φ hφ hf hi]
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (weak_endpoint_weight_integral ν πs π hlim t hds hd φ hi)

end RegularPointCoordinates

end

end OAI
