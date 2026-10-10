import OAI.Analysis.CircleDomains.Selection.PhysicalRealCoordinate
import OAI.Analysis.CircleDomains.Sobolev.PlanarDifferentialEnergy
import OAI.Analysis.CircleDomains.Sobolev.SphericalWeightedCoarea
import OAI.Analysis.CircleDomains.Sobolev.FiniteSphericalArea

namespace OAI

/-! Apply weighted coarea to the actual smooth physical representative
of a quotient coordinate. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem physicalRealCoordinate_ae_finite_weighted_levels
    {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData X Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → X)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    (Q : PhysicalRealCoordinate d π)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐt ∂volume,
      (∫⁻y in d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈
        circleBandGraph d.quotientDomain Q.quotient},
        g y ∂(μH[1] : Measure Sphere)) < ∞ := by
  let e := Complex.equivRealProdCLM
  let D := ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hDc : D = e ⁻¹' FiniteTransfer.realChartDomain d.physicalDomain := by
    ext z
    change (z : Sphere) ∈ d.physicalDomain ↔
      (e.symm (e z) : Sphere) ∈ d.physicalDomain
    rw [e.symm_apply_apply]
  have hreal : IsOpen (FiniteTransfer.realChartDomain d.physicalDomain) :=
    hG.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)
  have hs : ContDiffOn ℝ 1 Q.physical (FiniteTransfer.realChartDomain d.physicalDomain) :=
    Q.physical_smooth.of_le (by simp)
  have hf : ContDiffOn ℝ 1 (Q.physical ∘ e) D := by
    rw [hDc]
    exact hs.comp e.contDiff.contDiffOn (fun _ hx => hx)
  have hf2 : (∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ (Q.physical ∘ e) z‖ ^ 2)) < ∞ := by
    rw [hDc]
    exact complex_chart_differential_energy_finite hreal hs Q.physical_energy
  obtain ⟨C, hC, hderiv⟩ := finite_sphere_chart_derivative_decay
  apply ae_finite_spherical_weighted_levels hcoarea hC hderiv hD hf hf2
    (fun t => d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈
      circleBandGraph d.quotientDomain Q.quotient}) _ g hg henergy
  intro t
  ext z
  have hzU (hz : (z : Sphere) ∈ d.physicalDomain) : π z ∈ d.quotientDomain := by
    rw [he ⟨z, hz⟩]
    exact (d.domainEquiv ⟨z, hz⟩).property
  constructor
  · rintro ⟨hz, ht⟩
    refine ⟨hz, ?_⟩
    change (Q.physical (e z) : UnitAddCircle) = t
    rw [Q.pullback z hz]
    exact (circleBandGraph_on_open hU Q.quotient_continuous (hzU hz)).mp ht
  · rintro ⟨hz, ht⟩
    refine ⟨hz, (circleBandGraph_on_open hU Q.quotient_continuous (hzU hz)).mpr ?_⟩
    change (Q.physical (e z) : UnitAddCircle) = t at ht
    rwa [Q.pullback z hz] at ht

theorem physicalRealCoordinate_ae_finite_level_length
    {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData X Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → X)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    (Q : PhysicalRealCoordinate d π) :
    ∀ᵐt ∂volume, (μH[1] : Measure Sphere)
      (d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈ circleBandGraph d.quotientDomain Q.quotient}) < ∞ := by
  have henergy : (∫⁻_ : Sphere, (1 : ℝ≥0∞) ^ 2 ∂sphericalArea) < ∞ := by simp
  simpa only [lintegral_one, Measure.restrict_apply_univ] using
    physicalRealCoordinate_ae_finite_weighted_levels hcoarea d hU hG π he Q
      (fun _ => 1) measurable_const henergy

end CircleDomainRigidity

end

end OAI
