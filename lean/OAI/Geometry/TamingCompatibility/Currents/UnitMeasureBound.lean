import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothUnitEvaluation

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]
attribute [local instance] unitMeasurable unitBorel unitT2

lemma unitMeasureCurrent_bound [CompactSpace X] [T2Space X]
    (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsProbabilityMeasure μ]
    (α : ManifoldForms.smoothForms X 2) :
    ‖unitMeasureCurrent J g μ α‖ ≤ ‖smoothUnitEvaluation J g α‖ := by
  change ‖∫ p, smoothUnitEvaluation J g α p ∂μ‖ ≤ _
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall (fun p => (smoothUnitEvaluation J g α).norm_coe_le_norm p))

lemma unitMeasureCurrent_normalized [CompactSpace X] [T2Space X]
    (J : AlmostComplexStructure X) (α : TwoForm X) (hα : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hα ht))) [IsProbabilityMeasure μ] :
    unitMeasureCurrent J (hermitianMetric J α hα ht) μ
      ⟨invariantPart J α, hα.invariantPart J⟩ = 1 := by
  change (∫ p, unitEvaluation J (hermitianMetric J α hα ht)
    (invariantPart J α) (hα.invariantPart J) p ∂μ) = 1
  rw [hermitianMetric_unitEvaluation]
  simp

theorem exists_geometric_separating_current [CompactSpace X] [T2Space X] [Nonempty X]
    (J : AlmostComplexStructure X) (α : TwoForm X) (hα : IsSmooth α) (ht : Tames α J)
    (hn : ¬ ∃ η : TwoForm X, IsSymplectic η ∧ Compatible η J) :
    ∃ μ : Measure (MetricUnit (hermitianMetric J α hα ht)),
      ∃ hμ : IsProbabilityMeasure μ,
      letI := hμ
      μ.Regular ∧
      let P := unitMeasureCurrent J (hermitianMetric J α hα ht) μ
      P ⟨invariantPart J α, hα.invariantPart J⟩ = 1 ∧
      (∀ β : ManifoldForms.smoothForms X 2,
        IsClosed β.val → IsInvariant β.val J → P β = 0) ∧
      (∀ β : ManifoldForms.smoothForms X 2, Tames β.val J → 0 < P β) := by
  obtain ⟨μ, hμ, hr, hz⟩ := exists_geometric_separating_probability J
    (hermitianMetric J α hα ht) hn
  let := hμ
  refine ⟨μ, hμ, hr, unitMeasureCurrent_normalized J α hα ht μ, ?_, ?_⟩
  · intro β hβc hβi
    exact hz β.val β.property hβc hβi
  · intro β hβ
    exact unitMeasureCurrent_pos J _ μ β.val β.property hβ

end TamingCompatibility

end

end OAI
