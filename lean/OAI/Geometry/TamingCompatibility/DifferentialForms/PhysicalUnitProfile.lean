import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.PhysicalProfile

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms Set
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)

lemma physicalProfile_unit_pair_continuous {r : ℝ} (hr : 0 < r) :
    Continuous (fun vu : MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht) =>
      physicalProfile J α hs ht r vu.1.val.proj vu.2.val.proj) := by
  let := geometricMetricSpace J α hs ht
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have h₁ : Continuous (fun vu : MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht) => vu.1.val.proj) :=
    hp.comp continuous_fst
  have h₂ : Continuous (fun vu : MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht) => vu.2.val.proj) :=
    hp.comp continuous_snd
  change Continuous (fun vu : MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht) =>
    ((1+dist vu.1.val.proj vu.2.val.proj/r)⁻¹)^6)
  exact ((continuous_const.add ((h₁.dist h₂).div_const r)).inv₀
    (fun vu => (show 0 < 1+dist vu.1.val.proj vu.2.val.proj/r by positivity).ne')).pow 6
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
open Set MeasureTheory
namespace TamingCompatibility
lemma continuous_double_integral_lower
    {Y Z : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopologyEither Y Z]
    (ν : Measure Y) (μ : Measure Z) [IsFiniteMeasure ν] [IsProbabilityMeasure μ]
    (p k : Y × Z → ℝ) (hp : Continuous p) (hk : Continuous k)
    (C B : ℝ) (h : ∀ y z, -C*p (y,z)-B ≤ k (y,z)) :
    -C*(∫ y, ∫ z, p (y,z) ∂μ ∂ν)-B*ν.real univ ≤ ∫ y, ∫ z, k (y,z) ∂μ ∂ν := by
  have hi : Integrable p (ν.prod μ) := hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hki : Integrable k (ν.prod μ) := hk.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh (y : Y) : -C*(∫ z, p (y,z) ∂μ)-B ≤ ∫ z, k (y,z) ∂μ := by
    have hpi : Integrable (fun z => p (y,z)) μ :=
      (hp.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hki : Integrable (fun z => k (y,z)) μ :=
      (hk.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hh := integral_mono ((hpi.const_mul (-C)).sub (integrable_const B)) hki (h y)
    simp only [Pi.sub_apply] at hh
    simpa only [integral_sub (hpi.const_mul (-C)) (integrable_const B),integral_const_mul,
      integral_const,probReal_univ,one_smul] using hh
  have hh' := integral_mono ((hi.integral_prod_left.const_mul (-C)).sub (integrable_const B))
    hki.integral_prod_left hh
  simp only [Pi.sub_apply] at hh'
  simpa only [integral_sub (hi.integral_prod_left.const_mul (-C)) (integrable_const B),integral_const_mul,
    integral_const,smul_eq_mul,mul_comm (ν.real univ)] using hh'
end TamingCompatibility

end
end

end OAI
