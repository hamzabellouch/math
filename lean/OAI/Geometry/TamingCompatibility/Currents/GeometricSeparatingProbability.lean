import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ClosedUnitEvaluation
import OAI.Geometry.TamingCompatibility.Charts.BundleTotalSpaceT2

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

local instance unitT2 [T2Space X] (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) : T2Space (MetricUnit g) := by
  let : T2Space (TangentBundle Model X) := bundle_totalSpace_t2 (TangentSpace Model : X → Type)
  infer_instance

local instance unitMeasurable (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) : MeasurableSpace (MetricUnit g) := borel _
local instance unitBorel (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) : BorelSpace (MetricUnit g) := ⟨rfl⟩

theorem exists_geometric_separating_probability [CompactSpace X] [T2Space X] [Nonempty X]
    (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (hno : ¬ ∃ α : TwoForm X, IsSymplectic α ∧ Compatible α J) :
    ∃ μ : Measure (MetricUnit g), IsProbabilityMeasure μ ∧ μ.Regular ∧
      ∀ (α : TwoForm X) (hα : IsSmooth α), IsClosed α → IsInvariant α J →
        ∫ p, unitEvaluation J g α hα p ∂μ = 0 := by
  let L := LinearMap.range (closedUnitEvaluation J g)
  have hd : Disjoint (positiveFunctions (K := MetricUnit g)) (L : Set C(MetricUnit g, ℝ)) := by
    rw [Set.disjoint_left]
    intro f hf hL
    obtain ⟨α, rfl⟩ := hL
    have ht : Tames α.val J :=
      (tames_iff_unitEvaluation_pos J g α.val α.property.1).mpr hf
    exact hno ⟨α.val, ⟨α.property.1, α.property.2.1, ht.isNondegenerate⟩,
      ht, α.property.2.2⟩
  obtain ⟨μ, hμ, hreg, hann⟩ := exists_probability_annihilating_subspace L hd
  refine ⟨μ, hμ, hreg, ?_⟩
  intro α hα hc hi
  exact hann _ ⟨⟨α, hα, hc, hi⟩, rfl⟩

end TamingCompatibility

end

end OAI
