import OAI.Analysis.CircleDomains.Topology.MeanSigmaCompactPhysicalCount
import OAI.Analysis.CircleDomains.Modulus.SphericalChartCost
import OAI.Analysis.CircleDomains.Topology.SphereSliceChart

namespace OAI

/-! Finite generic intersections on a bounded physical chart follow
from the actual L2 occupation density and the coordinate's differential
energy. No simplicity of the sampled path is needed.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem mean_real_chart_circle_count_finite
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {A D K : Set ℂ} (hA : IsSigmaCompact A) (hK : IsCompact K) (hAK : A ⊆ K)
    (hAG : ∀ z ∈ A, (z : Sphere) ∈ G) (hAD : A ⊆ D) (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (henergy : (∫⁻ z in D, ENNReal.ofReal ‖fderiv ℝ f z‖ ^ 2) < ∞)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (hfinite : ∀ᵐ γ ∂(μ : Measure _), physicalDomainLength e y₀ γ < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻ t : UnitAddCircle, ∫⁻ γ,
      pathImageCount ((fun z : ℂ => π (z : Sphere)) '' (A ∩ {z | (f z : UnitAddCircle) = t}))
        γ ∂(μ : Measure _)) < ∞ := by
  obtain ⟨B, hB⟩ := finiteCoord_lipschitz_on_compact_chart hK
  have hAm : MeasurableSet A := by
    obtain ⟨Q, hQ, hcov⟩ := hA
    rw [← hcov]
    exact MeasurableSet.iUnion fun n => (hQ n).measurableSet
  have hcoeA : MeasurableSet (((↑) : ℂ → Sphere) '' A) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hAm
  let k : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ‖fderiv ℝ f z‖
  let g := localizedSphericalChartWeight B A k
  have hk : Measurable k := (measurable_fderiv ℝ f).norm.ennreal_ofReal
  have hg : Measurable g := measurable_localizedSphericalChartWeight B hAm hk
  have hg2 : (∫⁻ y, g y ^ 2 ∂sphericalArea) < ∞ :=
    localizedSphericalChartWeight_square_finite B hAm hk
      ((lintegral_mono_set hAD).trans_lt henergy)
  have hcost : (∫⁻ y, g y ∂meanPhysicalOccupation e y₀ μ) < ∞ := by
    rw [← lintegral_physicalOccupationCode e hU y₀ μ g hg]
    exact (lintegral_physical_cost_le_square_norms e hU y₀ μ sphericalArea ρ g hρ hg hocc).trans_lt
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hρ2.ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg2.ne))
  have hbound := mean_sigmaCompact_physical_chart_circle_count_le hcoarea e hU y₀ π hπ he
    ((↑) : ℂ → Sphere) OnePoint.continuous_coe hA hAG hAD hD finiteCoord
    measurable_finiteCoord (fun z _ => finiteCoord_coe z) B (hB.mono (image_mono hAK))
    μ hfinite hf
  have hi : (∫⁻ t in Ico (0 : ℝ) 1, ∫⁻ γ,
      pathImageCount ((fun z : ℂ => π (z : Sphere)) ''
        (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)})) γ ∂(μ : Measure _)) < ∞ := by
    apply hbound.trans_lt
    simpa only [g, localizedSphericalChartWeight, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
      lintegral_indicator hcoeA] using hcost
  have hc := measurable_sigmaCompact_chart_circle_count
    (fun z : ℂ => π (z : Sphere)) (hπ.comp OnePoint.continuous_coe) hA f
      (hf.continuousOn.mono hAD)
  have hm := (hc.comp measurable_swap).lintegral_prod_right' (ν := (μ : Measure _))
  have heq := (AddCircle.measurePreserving_mk (1 : ℝ) 0).lintegral_comp hm
  rw [restrict_Ico_eq_restrict_Ioc] at hi
  simp only [zero_add] at heq
  dsimp only [Function.comp_def, Prod.swap] at heq
  exact heq ▸ hi

theorem ae_real_chart_circle_count_finite
    (π : Sphere → Sphere) (hπ : Continuous π) {A : Set ℂ} (hA : IsSigmaCompact A)
    (f : ℂ → ℝ) (hf : ContinuousOn f A)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (hmean : (∫⁻ t : UnitAddCircle, ∫⁻ γ,
      pathImageCount ((fun z : ℂ => π (z : Sphere)) '' (A ∩ {z | (f z : UnitAddCircle) = t}))
        γ ∂(μ : Measure _)) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _), ∀ᵐ t : UnitAddCircle ∂volume,
      pathImageCount ((fun z : ℂ => π (z : Sphere)) '' (A ∩ {z | (f z : UnitAddCircle) = t})) γ < ∞ := by
  have hc := measurable_sigmaCompact_chart_circle_count
    (fun z : ℂ => π (z : Sphere)) (hπ.comp OnePoint.continuous_coe) hA f hf
  have hm := (hc.comp measurable_swap).lintegral_prod_right' (ν := (μ : Measure _))
  have hg : ∀ᵐ t : UnitAddCircle ∂volume, ∀ᵐ γ ∂(μ : Measure _),
      pathImageCount ((fun z : ℂ => π (z : Sphere)) '' (A ∩ {z | (f z : UnitAddCircle) = t})) γ < ∞ := by
    filter_upwards [ae_lt_top hm hmean.ne] with t ht
    exact ae_lt_top (hc.comp (measurable_id.prodMk measurable_const)) ht.ne
  have hmeas : MeasurableSet {p : C(PathTime, Sphere) × UnitAddCircle |
      pathImageCount ((fun z : ℂ => π (z : Sphere)) ''
        (A ∩ {z | (f z : UnitAddCircle) = p.2})) p.1 < ∞} :=
    measurableSet_lt hc measurable_const
  exact (Measure.ae_ae_comm hmeas).mpr hg

end CircleDomainRigidity

end

end OAI
