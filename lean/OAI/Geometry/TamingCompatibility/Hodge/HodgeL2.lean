import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothCommutator
import OAI.Geometry.TamingCompatibility.Hodge.HodgePairing
import OAI.Geometry.TamingCompatibility.Hodge.HodgePairingIntegral

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def l2CurrentSource (Q : L2 A J α hs ht true) : PreL2 A J α hs ht true →ₗ[ℝ] ℝ where
  toFun a := ⟪Q,smoothL2 A J α hs ht true a⟫
  map_add' a b := by rw [map_add,inner_add_right]
  map_smul' t a := by rw [map_smul,inner_smul_right]; rfl

omit [T2Space X] in
lemma hodgeRegularization_l2_represents (Q : L2 A J α hs ht true) {r : ℝ} (hr : 0 < r) :
    hodgeCubeRepresents A J α hs ht r (l2CurrentSource A J α hs ht Q)
      (hodgeRegularization A J α hs ht r Q) := by
  intro a
  rw [hodgeRegularization_symmetric,hodgeRegularization_smoothShift_cube A J α hs ht r hr]
  rfl

omit [T2Space X] in
lemma hodgeRegularization_anti_source (Q : L2 A J α hs ht true)
    (hQ : l2AntiProjection A J α hs ht Q = Q) {r : ℝ} (hr : 0 < r)
    (a : PreL2 A J α hs ht true) :
    ⟪hodgeRegularization A J α hs ht r Q,
      smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
        (a-preAntiProjection A J α hs ht a))⟫ = 0 := by
  rw [hodgeRegularization_l2_represents A J α hs ht Q hr]
  change ⟪Q,smoothL2 A J α hs ht true (a-preAntiProjection A J α hs ht a)⟫ = 0
  rw [map_sub,inner_sub_right,preAntiProjection_smooth,←l2AntiProjection_self_adjoint,hQ,sub_self]
end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2

def positiveL2Source (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    PreL2 A J α hs ht true →ₗ[ℝ] ℝ := unitMeasureCurrent J (hermitianMetric J α hs ht) μ

lemma positiveL2Source_represents
    (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
    (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr) :
    hodgeCubeRepresents A J α hs ht r (positiveL2Source A J α hs ht μ)
      (S.regularize (hermitianMetric J α hs ht) μ) := S.regularize_cubeRepresents _ μ
end TamingCompatibility.GeometricHilbert

end
end

end OAI
