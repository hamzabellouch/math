import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.SmoothCorrection
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothCommutator
import OAI.Geometry.TamingCompatibility.Hodge.HodgePairing

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in
lemma hodgeSmoothShift_cube_bijective (r : ℝ) (hr : 0 < r) :
    Function.Bijective (fun a : PreL2 A J α hs ht true => (hodgeSmoothShift A J α hs ht r ^ 3) a) := by
  constructor
  · intro a b hab
    dsimp only at hab
    apply (smoothL2 A J α hs ht true).injective
    rw [← hodgeRegularization_smoothShift_cube A J α hs ht r hr a,
      ← hodgeRegularization_smoothShift_cube A J α hs ht r hr b,hab]
  · intro b
    obtain ⟨a,ha⟩ := hodgeRegularization_smooth A J α hs ht D hD r hr b
    exact ⟨a,hodgeRegularization_smooth_inverse A J α hs ht r hr b a ha⟩

def hodgeSmoothInverse (r : ℝ) (hr : 0 < r) :
    PreL2 A J α hs ht true ≃ₗ[ℝ] PreL2 A J α hs ht true :=
  (LinearEquiv.ofBijective (hodgeSmoothShift A J α hs ht r ^ 3)
    (hodgeSmoothShift_cube_bijective A J α hs ht D hD r hr)).symm

lemma hodgeSmoothInverse_left (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    hodgeSmoothInverse A J α hs ht D hD r hr ((hodgeSmoothShift A J α hs ht r ^ 3) a) = a :=
  (LinearEquiv.ofBijective _ (hodgeSmoothShift_cube_bijective A J α hs ht D hD r hr)).symm_apply_apply a
lemma hodgeSmoothInverse_right (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    (hodgeSmoothShift A J α hs ht r ^ 3) (hodgeSmoothInverse A J α hs ht D hD r hr a) = a :=
  (LinearEquiv.ofBijective _ (hodgeSmoothShift_cube_bijective A J α hs ht D hD r hr)).apply_symm_apply a

lemma hodgeSmoothInverse_spec (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    smoothL2 A J α hs ht true (hodgeSmoothInverse A J α hs ht D hD r hr a) =
      hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true a) := by
  rw [← hodgeSmoothInverse_right A J α hs ht D hD r hr a,
    hodgeRegularization_smoothShift_cube A J α hs ht r hr,
    hodgeSmoothInverse_left]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def hodgeDistributionInverse (r : ℝ) (hr : 0 < r)
    (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) : L2 A J α hs ht true :=
  (InnerProductSpace.toDual ℝ (L2 A J α hs ht true)).symm
    ((F.comp (hodgeSmoothInverse A J α hs ht D hD r hr).toLinearMap).extendOfNorm
      (smoothL2 A J α hs ht true).toLinearMap)

lemma hodgeDistributionInverse_bound (r : ℝ) (hr : 0 < r)
    (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ a, ‖F a‖ ≤ K*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖) :
    ‖hodgeDistributionInverse A J α hs ht D hD r hr F‖ ≤ K := by
  rw [hodgeDistributionInverse,(InnerProductSpace.toDual ℝ (L2 A J α hs ht true)).symm.norm_map]
  apply LinearMap.opNorm_extendOfNorm_le (smoothL2_dense A J α hs ht true) hK
  intro b
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,hodgeSmoothInverse_right,
    LinearIsometry.coe_toLinearMap] using hF (hodgeSmoothInverse A J α hs ht D hD r hr b)

lemma hodgeDistributionInverse_represents (r : ℝ) (hr : 0 < r)
    (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) (K : ℝ)
    (hF : ∀ a, ‖F a‖ ≤ K*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖) :
    hodgeCubeRepresents A J α hs ht r F
      (hodgeDistributionInverse A J α hs ht D hD r hr F) := by
  intro a
  rw [hodgeDistributionInverse,InnerProductSpace.toDual_symm_apply]
  have hb : ∃ K : ℝ, ∀ b : PreL2 A J α hs ht true,
      ‖(F.comp (hodgeSmoothInverse A J α hs ht D hD r hr).toLinearMap) b‖ ≤
        K*‖smoothL2 A J α hs ht true b‖ := by
    exact ⟨K,fun b => by simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,
      hodgeSmoothInverse_right] using hF (hodgeSmoothInverse A J α hs ht D hD r hr b)⟩
  have he := LinearMap.extendOfNorm_eq (smoothL2_dense A J α hs ht true) hb
    ((hodgeSmoothShift A J α hs ht r^3) a)
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,hodgeSmoothInverse_left,
    LinearIsometry.coe_toLinearMap] using he

include D hD in
lemma hodgeCubeRepresents_unique (r : ℝ) (hr : 0 < r)
    (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) (U V : L2 A J α hs ht true)
    (hU : hodgeCubeRepresents A J α hs ht r F U)
    (hV : hodgeCubeRepresents A J α hs ht r F V) : U = V := by
  apply ext_inner_right ℝ
  intro b
  refine (smoothL2_dense A J α hs ht true).induction_on b
    (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
  intro a
  obtain ⟨c,rfl⟩ := (hodgeSmoothShift_cube_bijective A J α hs ht D hD r hr).surjective a
  exact (hU c).trans (hV c).symm
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricHilbert
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel unitT2

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitMeasureCurrent_finite_bound
    (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (β : smoothForms X 2) :
    ‖unitMeasureCurrent J g μ β‖ ≤ μ.real univ * ‖smoothUnitEvaluation J g β‖ := by
  change ‖∫ p, smoothUnitEvaluation J g β p ∂μ‖ ≤ _
  exact (norm_integral_le_of_norm_le_const (μ := μ) (f := smoothUnitEvaluation J g β)
    (C := ‖smoothUnitEvaluation J g β‖)
    (Filter.Eventually.of_forall (fun p => (smoothUnitEvaluation J g β).norm_coe_le_norm p))).trans_eq
      (mul_comm _ _)

namespace GeometricHilbert
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def hodgeCorrectionSource
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] : PreL2 A J α hs ht true →ₗ[ℝ] ℝ :=
  -((unitMeasureCurrent J g μ).comp (B.comp (smoothAntiProjection A J α hs ht)))

lemma hodgeCorrectionSource_anti
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (a : PreL2 A J α hs ht true) :
    hodgeCorrectionSource A J α hs ht B g μ (preAntiProjection A J α hs ht a) =
      hodgeCorrectionSource A J α hs ht B g μ a := by
  have he : smoothAntiProjection A J α hs ht (preAntiProjection A J α hs ht a) =
      smoothAntiProjection A J α hs ht a := by
    apply Subtype.ext
    apply Subtype.ext
    exact antiInvariantPart_idempotent J a.val
  change -(unitMeasureCurrent J g μ (B _)) = -(unitMeasureCurrent J g μ (B _))
  rw [he]

omit [MeasurableSpace X] [BorelSpace X] in
lemma hodgeCorrectionSource_closed
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (hBc : ∀ f, IsClosed (B f).val)
    (hBR : ∀ f, antiInvariantPart J (B f).val = f.val.val)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J g μ β = 0) (a : smoothForms X 2) (hac : IsClosed a.val) :
    unitMeasureCurrent J g μ a+hodgeCorrectionSource A J α hs ht B g μ a = 0 := by
  let R := smoothAntiProjection A J α hs ht
  let C := B.comp R
  have hc : IsClosed (a-C a).val := by
    apply (mem_closedForms_iff (a-C a)).mp
    apply Submodule.sub_mem
    · exact (mem_closedForms_iff a).mpr hac
    · exact (mem_closedForms_iff (C a)).mpr (hBc (R a))
  have hi : IsInvariant (a-C a).val J := by
    apply invariant_of_anti_zero J
    have he : R (C a) = R a := by
      apply Subtype.ext
      apply Subtype.ext
      exact hBR (R a)
    have hz : R (a-C a) = 0 := by rw [map_sub,he,sub_self]
    exact congrArg (fun f : antiPre A J α hs ht => f.val.val) hz
  have hz := hann (a-C a) hc hi
  change unitMeasureCurrent J g μ a - unitMeasureCurrent J g μ (C a) = 0
  simpa only [map_sub] using hz

lemma hodgeCorrectionSource_bound
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (r C : ℝ)
    (hB : ∀ a : PreL2 A J α hs ht true,
      ‖smoothUnitEvaluation J g (B (smoothAntiProjection A J α hs ht a))‖ ≤
        C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖)
    (a : PreL2 A J α hs ht true) :
    ‖hodgeCorrectionSource A J α hs ht B g μ a‖ ≤
      (μ.real univ*C*(r⁻¹)^3)*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  change ‖-(unitMeasureCurrent J g μ (B (smoothAntiProjection A J α hs ht a)))‖ ≤ _
  rw [norm_neg]
  exact ((unitMeasureCurrent_finite_bound J g μ _).trans
    (mul_le_mul_of_nonneg_left (hB a) (measureReal_nonneg))).trans_eq (by ring)
end GeometricHilbert
end TamingCompatibility

end
end

end
end

end OAI
