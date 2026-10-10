import OAI.Analysis.CircleDomains.Rigidity.RealBandTagNullTrace
import OAI.Analysis.CircleDomains.Topology.QuotientLocalChart
import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationCost

namespace OAI

/-! Application of the local tag proof to a physical path law. The
inverse-chart bound and the finite payment measure are constructed from
the quotient neighborhood, the differential energy and the law's density.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem ae_parameter_real_band_tag_null_trace
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {G U V Flags : Set Sphere} (hG : IsOpen G) (hU : IsOpen U) (hdense : Dense U)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (e : G ≃ₜ U) (y₀ : Sphere) (he : ∀ y : G, (e y).val = π y.val)
    (hTD : IsTotallyDisconnected Uᶜ) (hbad : ∀ p ∈ Gᶜ, π p ∈ Uᶜ)
    (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ closure V) (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ U, |f z| ≤ M) (hf : ContinuousOn f U)
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere))) (((↑) : ℂ → Sphere) ⁻¹' G))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    {Z : Type*} [MeasurableSpace Z] (P : ProbabilityMeasure Z)
    (γmap : Z → C(PathTime, Sphere)) (hγmap : Measurable γmap)
    (μ : ProbabilityMeasure C(PathTime, Sphere)) (hμ : P.map γmap = μ)
    (hfinite : ∀ᵐ z ∂(P : Measure Z), physicalDomainLength e y₀ (γmap z) < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞)
    (hband : ∀ z ∈ Flags, ENNReal.ofReal
      (limsup f (𝓝[U] z) - liminf f (𝓝[U] z)) ≤ m z)
    (hmFree : ∀ z ∈ Uᶜ \ Flags, m z = 0)
    (T : Z → Set PathTime) (hT : ∀ z, IsOpen (T z))
    (trace : Sphere → ℝ)
    (htrace : ∀ z ∈ (Uᶜ \ Flags) ∩ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph U f) ↔ t = trace z)
    {c : ℝ} (hbranch : ∀ z ∈ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph U f) → t ∈ Ico c (c + 1))
    (hgood : ∀ᵐ z ∂(P : Measure Z), ∀ᵐ θ : UnitAddCircle ∂volume, ∀ t ∈ T z,
      γmap z t ∈ Uᶜ \ Flags → (γmap z t, θ) ∈ circleBandGraph U f →
      ¬ (connectedComponentIn {x | (x, θ) ∈ circleBandGraph U f} (γmap z t)).Nontrivial) :
    ∀ᵐ z ∂(P : Measure Z), volume ((trace ∘ γmap z) ''
      ((γmap z ⁻¹' (Uᶜ \ Flags)) ∩ (T z ∩ γmap z ⁻¹' V))) = 0 := by
  let O := ((↑) : ℂ → Sphere) ⁻¹' G
  let A := O ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V
  let v : ℂ → ℝ := fun z => f (π (z : Sphere))
  let k : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ‖fderiv ℝ v z‖
  have hO : IsOpen O := hG.preimage OnePoint.continuous_coe
  have hA : MeasurableSet A := (hO.inter (hV.preimage (hπ.comp OnePoint.continuous_coe))).measurableSet
  obtain ⟨L, hL⟩ := finiteCoord_lipschitz_quotient_neighborhood π hπ G V hinfty
  let g := localizedSphericalChartWeight L A k
  have hk : Measurable k := (measurable_fderiv ℝ v).norm.ennreal_ofReal
  have hg : Measurable g := measurable_localizedSphericalChartWeight L hA hk
  have hg2 : (∫⁻ y, g y ^ 2 ∂sphericalArea) < ∞ :=
    localizedSphericalChartWeight_square_finite L hA hk
      ((lintegral_mono_set inter_subset_left).trans_lt henergy)
  have hcost := ae_physical_and_visit_cost_finite e hU y₀ μ sphericalArea ρ g hρ hg hocc
    hρ2 hg2 m hm hweight hvisits
  have hcostZ : ∀ᵐ z ∂(P : Measure Z),
      (∫⁻ y, g y ∂physicalOccupationCode e y₀ (γmap z)) + boundaryToll (γmap z) m < ∞ := by
    have hmap : (P : Measure Z).map γmap = (μ : Measure C(PathTime, Sphere)) := by
      rw [← ProbabilityMeasure.toMeasure_map, hμ]
    exact ae_of_ae_map hγmap.aemeasurable (hmap.symm ▸ hcost)
  filter_upwards [hfinite, hcostZ, hgood] with z hγ hc hγgood
  let γp : FinitePhysicalPath e y₀ := ⟨γmap z, hγ⟩
  rw [physicalOccupationCode_eq e y₀ γp] at hc
  exact real_band_tag_null_trace (B := Uᶜ) (D := U) hsard hsch G π hπ hclosed hsurj hr
    hU.isClosed_compl hTD hbad (by simpa only [compl_compl] using (Subset.rfl : U ⊆ U)) hdense hU hV
    (fun h => hinfty (subset_closure h)) hFlags hM hf e hU y₀ he
    ((↑) : ℂ → Sphere) OnePoint.continuous_coe hA
    (OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hA)
    (fun _ hz => hz.1) inter_subset_left hO finiteCoord measurable_finiteCoord
    (fun z _ => finiteCoord_coe z) L hL γp (hT z) hv (fun _ _ => rfl)
    (fun x hx => quotient_neighborhood_chart_covers e π he
      (fun h => hinfty (subset_closure h)) x ⟨hx.1.2, hx.2⟩)
    m hband hmFree (fun _ hx => hx) trace htrace hbranch hγgood hc

end CircleDomainRigidity

end

end OAI
