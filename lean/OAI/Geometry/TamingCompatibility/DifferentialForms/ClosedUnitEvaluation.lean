import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.PositiveFunctions

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

lemma metric_normalize (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) (x : X) (v : TangentSpace Model x) (hv : v ≠ 0) :
    g.inner x ((Real.sqrt (g.inner x v v))⁻¹ • v)
      ((Real.sqrt (g.inner x v v))⁻¹ • v) = 1 := by
  have hp := g.pos x v hv
  have hs : Real.sqrt (g.inner x v v) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  simp only [map_smul, _root_.smul_apply, smul_eq_mul]
  field_simp
  nlinarith [Real.sq_sqrt hp.le]

instance [Nonempty X] (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) : Nonempty (MetricUnit g) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let : Nontrivial (TangentSpace Model x) := inferInstanceAs (Nontrivial Space)
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace Model x)
  exact ⟨⟨⟨x, (Real.sqrt (g.inner x v v))⁻¹ • v⟩, metric_normalize g x v hv⟩⟩

lemma tames_iff_unitEvaluation_pos (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (α : TwoForm X) (hα : IsSmooth α) :
    Tames α J ↔ ∀ p, 0 < unitEvaluation J g α hα p := by
  constructor
  · intro h p
    apply h p.val.proj p.val.2
    intro hz
    have hp := p.property
    rw [hz, map_zero] at hp
    norm_num at hp
  · intro h x v hv
    let c := (Real.sqrt (g.inner x v v))⁻¹
    have hu : g.inner x (c • v) (c • v) = 1 := metric_normalize g x v hv
    have hp := h ⟨⟨x, c • v⟩, hu⟩
    change 0 < eval α x (c • v) (J.endomorphism x (c • v)) at hp
    rw [← associatedBilinear_apply] at hp
    simp only [map_smul, _root_.smul_apply, smul_eq_mul] at hp
    rw [associatedBilinear_apply] at hp
    have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr (g.pos x v hv))
    exact (mul_pos_iff_of_pos_left hc).mp ((mul_pos_iff_of_pos_left hc).mp hp)

def closedUnitEvaluation (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    smoothClosedInvariantForms J →ₗ[ℝ] C(MetricUnit g, ℝ) where
  toFun α := unitEvaluation J g α.val α.property.1
  map_add' _ _ := by ext p; rfl
  map_smul' _ _ := by ext p; rfl

end TamingCompatibility

end

end OAI
