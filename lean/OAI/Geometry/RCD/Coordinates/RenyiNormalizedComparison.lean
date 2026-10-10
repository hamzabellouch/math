import OAI.Geometry.RCD.Transport.RenyiHomogeneity

namespace OAI

/-! # The normalized comparison for a separated subplan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem RenyiMaximizingPlan.normalized_subplan_comparison
    (μ : Measure X) [IsFiniteMeasure μ] {ν₀ ν₁ : Measure X} [IsProbabilityMeasure ν₀]
    {π κ σ : Measure C(Time,X)} [IsProbabilityMeasure π] [IsProbabilityMeasure σ]
    {t : Time} {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (hmax : RenyiMaximizingPlan μ ν₀ ν₁ π t q)
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hκ : κ≤π) (hκ0 : κ univ≠0)
    (ht : IsOptimalCoupling ((κ univ)⁻¹ • κ.map (fun γ => γ 0))
      ((κ univ)⁻¹ • κ.map (fun γ => γ 1)) (σ.map (fun γ => (γ 0,γ 1))))
    (hgs : ∀ᵐ γ ∂σ, IsGeodesic γ)
    (hsκ : (π-κ).map (fun γ => γ t) ⟂ₘ κ.map (fun γ => γ t))
    (hsσ : (π-κ).map (fun γ => γ t) ⟂ₘ σ.map (fun γ => γ t)) :
    (∫ x, ((σ.map (fun γ => γ t)).rnDeriv μ x).toReal^q ∂μ) ≤
      ∫ x, (((κ univ)⁻¹ • κ.map (fun γ => γ t)).rnDeriv μ x).toReal^q ∂μ := by
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have hκtop : κ univ≠∞ := measure_ne_top κ univ
  have hi : (κ univ)⁻¹≠∞ := ENNReal.inv_ne_top.mpr hκ0
  let : IsFiniteMeasure (κ univ • σ) := Measure.smul_finite _ hκtop
  let : IsFiniteMeasure ((κ univ)⁻¹ • κ.map (fun γ => γ t)) := Measure.smul_finite _ hi
  have hscaled : IsOptimalCoupling (κ.map (fun γ => γ 0)) (κ.map (fun γ => γ 1))
      ((κ univ • σ).map (fun γ => (γ 0,γ 1))) := by
    have hh := ht.smul hκ0 hκtop
    simpa only [Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable,
      smul_smul,ENNReal.mul_inv_cancel hκ0 hκtop,one_smul] using hh
  have hgeoscaled : ∀ᵐ γ ∂κ univ • σ, IsGeodesic γ :=
    hgs.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hsep : (π-κ).map (fun γ => γ t) ⟂ₘ (κ univ • σ).map (fun γ => γ t) := by
    rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable]
    exact hsσ.mono_ac Measure.AbsolutelyContinuous.rfl Measure.smul_absolutelyContinuous
  have hh := hmax.subplan_comparison μ hq0 hq1 hg hp hκ hscaled hgeoscaled hsκ hsep
  rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable,
    renyiPower_smul μ _ hκtop q] at hh
  have he : κ univ • ((κ univ)⁻¹ • κ.map (fun γ => γ t))=κ.map (fun γ => γ t) := by
    rw [smul_smul,ENNReal.mul_inv_cancel hκ0 hκtop,one_smul]
  rw [←he] at hh
  rw [renyiPower_smul μ _ hκtop q] at hh
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (ENNReal.toReal_pos hκ0 hκtop) q)).mp hh

end RegularPointCoordinates

end

end OAI
