import OAI.Geometry.RCD.Sobolev.WeakInverseDensity

namespace OAI

/-! # Exact endpoint chords converge along the dominated recovery sequence -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem measurable_path_sigma_nonpos {K N s : ℝ}
    (hK : K ≤ 0) (hN : 1 < N) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Measurable (fun γ : C(Time,X) => sigma K N s (dist (γ 0) (γ 1))) := by
  exact ((continuous_sigma_nonpos_length hK hN hs hs1).comp
    ((continuous_eval_const 0).nndist (continuous_eval_const 1))).measurable

theorem endpoint_chord_tendsto
    (μ ν₀ ν₁ : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁]
    [ν₀.WeaklyRegular] [ν₁.WeaklyRegular] (h0 : ν₀ ≪ μ) (h1 : ν₁ ≪ μ)
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (π : ProbabilityMeasure C(Time,X))
    (hlim : Tendsto πs atTop (𝓝 π))
    (hds : ∀ j, (πs j : Measure C(Time,X)).map (fun γ => γ 0) ≤ (2 : ℝ≥0∞) • ν₀ ∧
      (πs j : Measure C(Time,X)).map (fun γ => γ 1) ≤ (2 : ℝ≥0∞) • ν₁)
    (hd : (π : Measure C(Time,X)).map (fun γ => γ 0) ≤ (2 : ℝ≥0∞) • ν₀ ∧
      (π : Measure C(Time,X)).map (fun γ => γ 1) ≤ (2 : ℝ≥0∞) • ν₁)
    {K N : ℝ} (hK : K ≤ 0) (hN : 0 < N)
    (hi0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal^(-(1/N))) ν₀)
    (hi1 : Integrable (fun x => (ν₁.rnDeriv μ x).toReal^(-(1/N))) ν₁) (t : Time) :
    Tendsto (fun j => ∫⁻γ,
      sigma K (N+1) (1-(t:ℝ)) (dist (γ 0) (γ 1))*(ν₀.rnDeriv μ (γ 0))^(-(1/N))+
      sigma K (N+1) (t:ℝ) (dist (γ 0) (γ 1))*(ν₁.rnDeriv μ (γ 1))^(-(1/N))
      ∂(πs j : Measure C(Time,X))) atTop
      (𝓝 (∫⁻γ,
      sigma K (N+1) (1-(t:ℝ)) (dist (γ 0) (γ 1))*(ν₀.rnDeriv μ (γ 0))^(-(1/N))+
      sigma K (N+1) (t:ℝ) (dist (γ 0) (γ 1))*(ν₁.rnDeriv μ (γ 1))^(-(1/N))
      ∂(π : Measure C(Time,X)))) := by
  have h0t := weak_inverse_density_distortion μ ν₀ h0 πs π hlim 0
    (fun j => (hds j).1) hd.1 hK hN (sub_nonneg.mpr t.property.2)
    (by linarith [t.property.1]) hi0
  have h1t := weak_inverse_density_distortion μ ν₁ h1 πs π hlim 1
    (fun j => (hds j).2) hd.2 hK hN t.property.1 t.property.2 hi1
  have hm0 := (measurable_path_sigma_nonpos (X:=X) hK (by linarith : 1<N+1)
    (sub_nonneg.mpr t.property.2) (by linarith [t.property.1])).mul
    (((ν₀.measurable_rnDeriv μ).comp (measurable_path_eval 0)).pow_const (-(1/N)))
  have hm1 := (measurable_path_sigma_nonpos (X:=X) hK (by linarith : 1<N+1)
    t.property.1 t.property.2).mul
    (((ν₁.measurable_rnDeriv μ).comp (measurable_path_eval 1)).pow_const (-(1/N)))
  change Measurable (fun γ : C(Time,X) => sigma K (N+1) (1-(t:ℝ)) (dist (γ 0) (γ 1))*
    (ν₀.rnDeriv μ (γ 0))^(-(1/N))) at hm0
  change Measurable (fun γ : C(Time,X) => sigma K (N+1) (t:ℝ) (dist (γ 0) (γ 1))*
    (ν₁.rnDeriv μ (γ 1))^(-(1/N))) at hm1
  simp_rw [lintegral_add_aux hm0 hm1]
  exact h0t.add h1t

end RegularPointCoordinates

end

end OAI
