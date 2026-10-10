import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothUnitEvaluation
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeResolventStar
import OAI.Geometry.TamingCompatibility.Hodge.HodgeLocalSmooth

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def hodgeSmoothShift (r : ℝ) : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true :=
  LinearMap.id + r^2 • hodgeLaplacian A J α hs ht

lemma hodgeSmoothShift_apply (r : ℝ) (a : PreL2 A J α hs ht true) :
    hodgeSmoothShift A J α hs ht r a = a + r^2 • hodgeLaplacian A J α hs ht a := rfl

lemma hodgeWeakSolution_smoothShift (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    hodgeWeakSolution A J α hs ht r hr
      (smoothL2 A J α hs ht true (hodgeSmoothShift A J α hs ht r a)) = hodgeSmooth A J α hs ht a := by
  apply (hodgeEnergy_coercive A J α hs ht r hr).continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [IsCoercive.continuousLinearEquivOfBilin_apply,
    IsCoercive.continuousLinearEquivOfBilin_apply,hodgeWeakSolution_identity_raw,
    hodgeSmoothShift_apply,map_add,map_smul,inner_add_left,real_inner_smul_left,
    hodgeLaplacian_green_weak,Variational.energy_apply,hodgeInclusion_smooth,
    hodgeScaledDerivative_apply,hodgeScaledDerivative_apply,real_inner_smul_left,real_inner_smul_right]
  ring

lemma hodgeResolvent_smoothShift (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    hodgeResolvent A J α hs ht r (smoothL2 A J α hs ht true (hodgeSmoothShift A J α hs ht r a)) =
      smoothL2 A J α hs ht true a := by
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply,
    hodgeWeakSolution_smoothShift,hodgeInclusion_smooth]

lemma hodgeRegularization_smoothShift_cube (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    hodgeRegularization A J α hs ht r
      (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)) =
      smoothL2 A J α hs ht true a := by
  change hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
    (hodgeResolvent A J α hs ht r (smoothL2 A J α hs ht true
      (hodgeSmoothShift A J α hs ht r (hodgeSmoothShift A J α hs ht r
        (hodgeSmoothShift A J α hs ht r a)))))) = _
  rw [hodgeResolvent_smoothShift A J α hs ht r hr,
    hodgeResolvent_smoothShift A J α hs ht r hr,hodgeResolvent_smoothShift A J α hs ht r hr]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma regularize_smoothShift_cube (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (a : PreL2 A J α hs ht true) :
    ⟪C.regularize g μ,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)⟫ =
      unitMeasureCurrent J g μ ⟨a.val,a.property⟩ := by
  rw [C.regularize_pair]
  change (∫ u, C.evaluation g u _ ∂μ) = ∫ u, unitEvaluation J g a.val a.property u ∂μ
  apply integral_congr_ae
  filter_upwards [] with u
  exact C.evaluation_smooth g u _ a (hodgeRegularization_smoothShift_cube A J α hs ht r hr a)
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def hodgeGraphResolvent (r : ℝ) (hr : 0 < r) :
    hodgeEnergy A J α hs ht →L[ℝ] hodgeEnergy A J α hs ht :=
  (hodgeWeakSolution A J α hs ht r hr).comp (hodgeInclusion A J α hs ht)

lemma hodgeWeakSolution_scale_transfer (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    hodgeWeakSolution A J α hs ht 1 zero_lt_one
      ((r^2)⁻¹ • f + (1-(r^2)⁻¹) • hodgeResolvent A J α hs ht r f) =
      hodgeWeakSolution A J α hs ht r hr f := by
  apply hodgeWeakSolution_unique
  intro v
  have he := hodgeWeakSolution_identity A J α hs ht r hr f v
  have hi : hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr f) =
      hodgeResolvent A J α hs ht r f := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  rw [hi,inner_add_left,real_inner_smul_left,real_inner_smul_left]
  have hn : r^2 ≠ 0 := pow_ne_zero 2 hr.ne'
  have hmul := congrArg ((r^2)⁻¹ * ·) he
  rw [mul_add,← mul_assoc,inv_mul_cancel₀ hn,one_mul] at hmul
  norm_num only [one_pow,one_mul]
  linarith

lemma hodgeGraphResolvent_scale_transfer (r : ℝ) (hr : 0 < r)
    (u : hodgeEnergy A J α hs ht) :
    hodgeGraphResolvent A J α hs ht 1 zero_lt_one
      ((r^2)⁻¹ • u + (1-(r^2)⁻¹) • hodgeGraphResolvent A J α hs ht r hr u) =
      hodgeGraphResolvent A J α hs ht r hr u := by
  change hodgeWeakSolution A J α hs ht 1 zero_lt_one
    (hodgeInclusion A J α hs ht (_+_)) = _
  rw [map_add,map_smul,map_smul]
  have hi : hodgeInclusion A J α hs ht (hodgeGraphResolvent A J α hs ht r hr u) =
      hodgeResolvent A J α hs ht r (hodgeInclusion A J α hs ht u) := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  rw [hi]
  exact hodgeWeakSolution_scale_transfer A J α hs ht r hr _
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
