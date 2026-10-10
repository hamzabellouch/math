import OAI.Analysis.CircleDomains.Topology.FiniteCircleChartIntersections
import OAI.Analysis.CircleDomains.Topology.QuotientLocalChart

namespace OAI

/-! A compact mask away from the image of infinity has a compact
physical inverse image. This converts the two-cut coarea estimate into
finite expected domain intersections of a masked period level. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem mean_masked_circle_domain_count_finite
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (M : Set Sphere) (hM : IsClosed M) (hinfty : π OnePoint.infty ∉ M)
    (H : UnitAddCircle → Set Sphere) (w : Sphere → UnitAddCircle)
    (hlevel : ∀ θ x, x ∈ U ∩ H θ → x ∈ M ∧ w x = θ)
    (D : Set ℂ) (hD : IsOpen D) (hDG : ∀ z ∈ D, (z : Sphere) ∈ G)
    (hcover : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ M → z ∈ D)
    (f : ℂ → UnitAddCircle) (hf : SmoothCircleOn f D)
    (hpullback : ∀ z ∈ D, f z = w (π (z : Sphere)))
    (henergy : (∫⁻ z in D, ENNReal.ofReal ‖circleFDeriv f z‖ ^ 2) < ∞)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (hfinite : ∀ᵐ γ ∂(μ : Measure _), physicalDomainLength e y₀ γ < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻ θ : UnitAddCircle, ∫⁻ γ, pathImageCount (U ∩ H θ) γ ∂(μ : Measure _)) < ∞ := by
  let K := ((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' M)
  have hK : IsCompact K := isCompact_finite_preimage (hM.preimage hπ) hinfty
  have hcuts : (0 : UnitAddCircle) ≠ ((1 / 2 : ℝ) : UnitAddCircle) := by
    intro heq
    have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have hhalf : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico h0 hhalf).mp heq
    norm_num at hh
  have hmean := mean_circle_chart_count_finite hcoarea e hU y₀ π hπ he hD hK
    (fun z hz => hDG z hz.2) hf henergy μ hfinite ρ hρ hocc hρ2 0 (1 / 2) hcuts
  apply lt_of_le_of_lt _ hmean
  apply lintegral_mono
  intro θ
  apply lintegral_mono
  intro γ
  apply pathImageCount_mono_target
  intro x hx
  have hxM := (hlevel θ x hx).1
  obtain ⟨z, hz, hzx⟩ := quotient_neighborhood_chart_covers e π he hinfty x ⟨hx.1, hxM⟩
  have hzD := hcover z hz.1 hz.2
  refine ⟨z, ⟨⟨hz.2, hzD⟩, ?_⟩, hzx⟩
  change f z = θ
  rw [hpullback z hzD, hzx]
  exact (hlevel θ x hx).2

end CircleDomainRigidity

end

end OAI
