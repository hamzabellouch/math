import OAI.Analysis.CircleDomains.Transfer.FiniteRealChartIntersections
import OAI.Analysis.CircleDomains.Selection.BandGraph
import OAI.Analysis.CircleDomains.Selection.FiniteLevelAssembly

namespace OAI

/-! A real coordinate that vanishes outside a compact finite-plane set
has finite generic intersections throughout the physical domain. The
single zero level also accounts for the physical point at infinity.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem real_domain_nonzero_level_subset
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U)
    (π : Sphere → Sphere) (he : ∀ y : G, (e y).val = π y.val)
    (f : Sphere → ℝ) (hf : ContinuousOn f U) {K : Set ℂ}
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ G → z ∉ K → f (π (z : Sphere)) = 0)
    (hinfty : OnePoint.infty ∈ G → f (π OnePoint.infty) = 0)
    {t : UnitAddCircle} (ht0 : t ≠ 0) :
    U ∩ {x | (x, t) ∈ circleBandGraph U f} ⊆
      (fun z : ℂ => π (z : Sphere)) ''
        ((K ∩ ((↑) : ℂ → Sphere) ⁻¹' G) ∩
          {z | (f (π (z : Sphere)) : UnitAddCircle) = t}) := by
  intro x hx
  let y := e.symm ⟨x, hx.1⟩
  have hy : π y.val = x := by rw [← he y]; exact congrArg Subtype.val (e.apply_symm_apply _)
  have hft : (f x : UnitAddCircle) = t := (circleBandGraph_on_open hU hf hx.1).mp hx.2
  cases hp : y.val using OnePoint.rec with
  | infty =>
      have hz : f x = 0 := by rw [← hy, hp]; exact hinfty (hp ▸ y.property)
      exact (ht0 (by simpa only [hz, AddCircle.coe_zero] using hft.symm)).elim
  | coe z =>
      have hzG : (z : Sphere) ∈ G := hp ▸ y.property
      have hzK : z ∈ K := by
        by_contra hn
        have hz : f x = 0 := by rw [← hy, hp]; exact hzero z hzG hn
        exact ht0 (by simpa only [hz, AddCircle.coe_zero] using hft.symm)
      refine ⟨z, ⟨⟨hzK, hzG⟩, ?_⟩, ?_⟩
      · change (f (π (z : Sphere)) : UnitAddCircle) = t
        rwa [← hp, hy]
      · change π (z : Sphere) = x
        rw [← hp, hy]

theorem ae_real_domain_circle_count_finite
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (hG : IsOpen G) (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (f : Sphere → ℝ) (hf : ContinuousOn f U)
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere))) (((↑) : ℂ → Sphere) ⁻¹' G))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ G → z ∉ K → f (π (z : Sphere)) = 0)
    (hinfty : OnePoint.infty ∈ G → f (π OnePoint.infty) = 0)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (hfinite : ∀ᵐ γ ∂(μ : Measure _), physicalDomainLength e y₀ γ < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _), ∀ᵐ t : UnitAddCircle ∂volume,
      pathImageCount (U ∩ {x | (x, t) ∈ circleBandGraph U f}) γ < ∞ := by
  let O := ((↑) : ℂ → Sphere) ⁻¹' G
  let A := K ∩ O
  let v : ℂ → ℝ := fun z => f (π (z : Sphere))
  have hO : IsOpen O := hG.preimage OnePoint.continuous_coe
  have hσ : IsSigmaCompact A := by
    let : LocallyCompactSpace O := hO.locallyCompactSpace
    have hσO : IsSigmaCompact O := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
    obtain ⟨Q, hQ, hcov⟩ := hσO
    refine ⟨fun n => K ∩ Q n, fun n => (hQ n).inter_left hK.isClosed, ?_⟩
    rw [← inter_iUnion, hcov]
  have hm := mean_real_chart_circle_count_finite hcoarea e hU y₀ π hπ he hσ hK
    inter_subset_left (fun _ hz => hz.2) inter_subset_right hO hv henergy μ hfinite ρ hρ hocc hρ2
  have ha := ae_real_chart_circle_count_finite π hπ hσ v
    (hv.continuousOn.mono inter_subset_right) μ hm
  have hz : (volume : Measure UnitAddCircle) {0} = 0 := by
    simpa only [image_singleton, AddCircle.coe_zero] using
      (volume_addCircle_image_eq_zero (show (volume : Measure ℝ) {0} = 0 from measure_singleton 0))
  have ha0 : ∀ᵐ t : UnitAddCircle ∂volume, t ≠ 0 :=
    ae_iff.mpr (by simpa only [not_not, ofPred_eq_eq_singleton] using hz)
  filter_upwards [ha] with γ hγ
  filter_upwards [hγ, ha0] with t ht ht0
  have hsub := real_domain_nonzero_level_subset e hU π he f hf hzero hinfty ht0
  exact (pathImageCount_mono_target hsub γ).trans_lt ht

theorem mean_real_domain_circle_count_finite
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (hG : IsOpen G) (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (f : Sphere → ℝ) (hf : ContinuousOn f U)
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere))) (((↑) : ℂ → Sphere) ⁻¹' G))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ G → z ∉ K → f (π (z : Sphere)) = 0)
    (hinfty : OnePoint.infty ∈ G → f (π OnePoint.infty) = 0)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (hfinite : ∀ᵐ γ ∂(μ : Measure _), physicalDomainLength e y₀ γ < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻ t : UnitAddCircle, ∫⁻ γ,
      pathImageCount (U ∩ {x | (x, t) ∈ circleBandGraph U f}) γ ∂(μ : Measure _)) < ∞ := by
  let O := ((↑) : ℂ → Sphere) ⁻¹' G
  let A := K ∩ O
  let v : ℂ → ℝ := fun z => f (π (z : Sphere))
  have hO : IsOpen O := hG.preimage OnePoint.continuous_coe
  have hσ : IsSigmaCompact A := by
    let : LocallyCompactSpace O := hO.locallyCompactSpace
    have hσO : IsSigmaCompact O := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
    obtain ⟨Q, hQ, hcov⟩ := hσO
    refine ⟨fun n => K ∩ Q n, fun n => (hQ n).inter_left hK.isClosed, ?_⟩
    rw [← inter_iUnion, hcov]
  have hm := mean_real_chart_circle_count_finite hcoarea e hU y₀ π hπ he hσ hK
    inter_subset_left (fun _ hz => hz.2) inter_subset_right hO hv henergy μ hfinite ρ hρ hocc hρ2
  have hz : (volume : Measure UnitAddCircle) {0} = 0 := by
    simpa only [image_singleton, AddCircle.coe_zero] using
      (volume_addCircle_image_eq_zero (show (volume : Measure ℝ) {0} = 0 from measure_singleton 0))
  have ha0 : ∀ᵐ t : UnitAddCircle ∂volume, t ≠ 0 :=
    ae_iff.mpr (by simpa only [not_not, ofPred_eq_eq_singleton] using hz)
  apply (show (∫⁻ t : UnitAddCircle, ∫⁻ γ,
      pathImageCount (U ∩ {x | (x, t) ∈ circleBandGraph U f}) γ ∂(μ : Measure _)) ≤
      (∫⁻ t : UnitAddCircle, ∫⁻ γ,
        pathImageCount ((fun z : ℂ => π (z : Sphere)) ''
          (A ∩ {z | (v z : UnitAddCircle) = t})) γ ∂(μ : Measure _)) from ?_).trans_lt hm
  apply lintegral_mono_ae
  filter_upwards [ha0] with t ht0
  apply lintegral_mono
  intro γ
  exact pathImageCount_mono_target
    (real_domain_nonzero_level_subset e hU π he f hf hzero hinfty ht0) γ

end CircleDomainRigidity

end

end OAI
