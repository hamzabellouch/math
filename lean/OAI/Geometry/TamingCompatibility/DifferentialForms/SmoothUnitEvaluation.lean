import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricCoords
import OAI.Geometry.TamingCompatibility.Currents.GeometricSeparatingProbability

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

lemma eval_antiInvariantPart_complexLine (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (v : TangentSpace Model x) :
    eval (antiInvariantPart J α) x v (J.endomorphism x v) = 0 := by
  have h := congrArg (fun β => eval β x v (J.endomorphism x v))
    (invariantPart_add_antiInvariantPart J α)
  change eval (invariantPart J α) x v (J.endomorphism x v) +
    eval (antiInvariantPart J α) x v (J.endomorphism x v) = _ at h
  rw [eval_invariantPart_complexLine] at h
  linarith

def smoothUnitEvaluation (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    ManifoldForms.smoothForms X 2 →ₗ[ℝ] C(MetricUnit g, ℝ) where
  toFun α := unitEvaluation J g α.val α.property
  map_add' _ _ := by ext p; rfl
  map_smul' _ _ := by ext p; rfl

def unitMeasureCurrent [CompactSpace X] [T2Space X]
    (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] :
    ManifoldForms.smoothForms X 2 →ₗ[ℝ] ℝ where
  toFun α := ∫ p, smoothUnitEvaluation J g α p ∂μ
  map_add' α β := by
    simp only [map_add, ContinuousMap.add_apply]
    exact integral_add
      ((smoothUnitEvaluation J g α).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((smoothUnitEvaluation J g β).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  map_smul' c α := by
    simp only [map_smul, ContinuousMap.smul_apply, RingHom.id_apply]
    exact integral_smul _ _

lemma unitMeasureCurrent_antiInvariantPart [CompactSpace X] [T2Space X]
    (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (α : TwoForm X) (hα : IsSmooth α) :
    unitMeasureCurrent J g μ ⟨antiInvariantPart J α, hα.antiInvariantPart J⟩ = 0 := by
  change (∫ p : MetricUnit g,
    eval (antiInvariantPart J α) p.val.proj p.val.2
      (J.endomorphism p.val.proj p.val.2) ∂μ) = 0
  simp only [eval_antiInvariantPart_complexLine, integral_zero]

lemma unitMeasureCurrent_pos [CompactSpace X] [T2Space X]
    (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsProbabilityMeasure μ]
    (α : TwoForm X) (hα : IsSmooth α) (ht : Tames α J) :
    0 < unitMeasureCurrent J g μ ⟨α, hα⟩ := by
  let f := unitEvaluation J g α hα
  have hf : ∀ p, 0 < f p := (tames_iff_unitEvaluation_pos J g α hα).mp ht
  have hi := f.continuous.integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace f)
  change 0 < ∫ p, f p ∂μ
  rw [integral_pos_iff_support_of_nonneg (fun p => (hf p).le) hi]
  have hs : Function.support f = Set.univ := by
    ext p
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hf p).ne'
  rw [hs, measure_univ]
  exact zero_lt_one

lemma hermitianMetric_unitEvaluation (J : AlmostComplexStructure X)
    (α : TwoForm X) (hα : IsSmooth α) (ht : Tames α J) :
    unitEvaluation J (hermitianMetric J α hα ht)
      (invariantPart J α) (hα.invariantPart J) = 1 := by
  ext p
  change eval (invariantPart J α) p.val.proj p.val.2
    (J.endomorphism p.val.proj p.val.2) = 1
  rw [← associatedBilinear_apply]
  exact p.property

end TamingCompatibility

end

end OAI
