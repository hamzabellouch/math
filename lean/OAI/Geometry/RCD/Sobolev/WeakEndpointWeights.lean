import OAI.Geometry.RCD.Metric.EndpointWeightApproximation

namespace OAI

/-! # Weak convergence with a fixed integrable endpoint weight -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem weak_endpoint_weight_integral
    (ν : Measure X) [IsFiniteMeasure ν] [ν.WeaklyRegular]
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (π : ProbabilityMeasure C(Time,X))
    (hlim : Tendsto πs atTop (𝓝 π)) (t : Time)
    (hds : ∀ j, (πs j : Measure C(Time,X)).map (fun γ => γ t)≤(2 : ℝ≥0∞) • ν)
    (hd : (π : Measure C(Time,X)).map (fun γ => γ t)≤(2 : ℝ≥0∞) • ν)
    (φ : C(Time,X) →ᵇ ℝ) {g : X → ℝ} (hg : Integrable g ν) :
    Tendsto (fun j => ∫γ,φ γ*g (γ t) ∂(πs j : Measure C(Time,X))) atTop
      (𝓝 (∫γ,φ γ*g (γ t) ∂(π : Measure C(Time,X)))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε/(8*(‖φ‖+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨f,herr,hf⟩ := hg.exists_boundedContinuous_integral_sub_le hδ
  let ψ : C(Time,X) →ᵇ ℝ := φ*(f.compContinuous ⟨fun γ => γ t,continuous_eval_const t⟩)
  have ht : Tendsto (fun j => ∫γ,φ γ*f (γ t) ∂(πs j : Measure C(Time,X))) atTop
      (𝓝 (∫γ,φ γ*f (γ t) ∂(π : Measure C(Time,X)))) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction ψ).continuousAt.tendsto.comp hlim
  obtain ⟨J,hJ⟩ := Metric.tendsto_atTop.mp ht (ε/2) (by positivity)
  have hsmall : 4*‖φ‖*δ<ε/2 := by
    have heq : (8*(‖φ‖+1))*δ=ε := by dsimp [δ]; field_simp
    nlinarith [norm_nonneg φ]
  refine ⟨J,fun j hj => ?_⟩
  have hleft := (integral_endpoint_weight_error (πs j : Measure C(Time,X)) ν t (hds j) φ hg hf).trans
    (mul_le_mul_of_nonneg_left herr (by positivity : 0≤2*‖φ‖))
  have hright := (integral_endpoint_weight_error (π : Measure C(Time,X)) ν t hd φ hg hf).trans
    (mul_le_mul_of_nonneg_left herr (by positivity : 0≤2*‖φ‖))
  have hmid := hJ j hj
  rw [dist_eq_norm] at hmid ⊢
  have htri := norm_add_le
    ((∫γ,φ γ*g (γ t) ∂(πs j : Measure C(Time,X)))-
      (∫γ,φ γ*f (γ t) ∂(πs j : Measure C(Time,X))))
    ((∫γ,φ γ*f (γ t) ∂(πs j : Measure C(Time,X)))-
      (∫γ,φ γ*g (γ t) ∂(π : Measure C(Time,X))))
  have htri' := norm_add_le
    ((∫γ,φ γ*f (γ t) ∂(πs j : Measure C(Time,X)))-
      (∫γ,φ γ*f (γ t) ∂(π : Measure C(Time,X))))
    ((∫γ,φ γ*f (γ t) ∂(π : Measure C(Time,X)))-
      (∫γ,φ γ*g (γ t) ∂(π : Measure C(Time,X))))
  rw [sub_add_sub_cancel] at htri htri'
  rw [norm_sub_rev] at hright
  linarith

end RegularPointCoordinates

end

end OAI
