import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeMixing
import OAI.Geometry.TamingCompatibility.Hodge.HodgeLiftUnitBound
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothInverse

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

def hodgeCorrectionRegularize
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (r : ℝ) (hr : 0 < r) :
    L2 A J α hs ht true :=
  hodgeDistributionInverse A J α hs ht D hD r hr (hodgeCorrectionSource A J α hs ht B g μ)

theorem exists_regularizable_closed_lift
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    ∃ B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2,
      (∀ f, IsClosed (B f).val) ∧
      (∀ f, antiInvariantPart J (B f).val = f.val.val) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ],
        ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
          hodgeCubeRepresents A J α hs ht r (hodgeCorrectionSource A J α hs ht B g μ)
            (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr) ∧
          ‖hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr‖ ≤ μ.real univ*C*(r⁻¹)^3 := by
  obtain ⟨B,hBc,hBR,C,hC,hB⟩ := exists_closed_lift_hodge_bound A J α hs ht D hD g
  refine ⟨B,hBc,hBR,C,hC,fun μ _ r hr hr1 => ?_⟩
  have hb := hodgeCorrectionSource_bound A J α hs ht B g μ r C (hB r hr hr1)
  exact ⟨hodgeDistributionInverse_represents A J α hs ht D hD r hr _ _ hb,
    hodgeDistributionInverse_bound A J α hs ht D hD r hr _ _ (by positivity) hb⟩

include D hD in

lemma hodgeCorrectionRegularize_mixing :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
        (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
        (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ],
        hodgeCubeRepresents A J α hs ht r (hodgeCorrectionSource A J α hs ht B g μ)
          (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr) →
        ‖hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr -
          l2AntiProjection A J α hs ht (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr)‖ ≤
          L*r*‖hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr‖ := by
  obtain ⟨L,hL,hb⟩ := hodge_relative_complement A J α hs ht D hD
  refine ⟨L,hL,fun r hr hr1 B g μ _ hrep => hb r hr hr1 _ ?_⟩
  intro a
  rw [hrep,map_sub,hodgeCorrectionSource_anti,sub_self]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

omit [T2Space X] in
lemma l2AntiProjection_star (a : L2 A J α hs ht true) :
    l2AntiProjection A J α hs ht (l2Star A J α hs ht a) = l2AntiProjection A J α hs ht a := by
  apply ext_inner_right ℝ
  intro b
  rw [l2AntiProjection_self_adjoint,l2Star_self_adjoint,l2AntiProjectionStar,
    l2AntiProjection_self_adjoint]

omit [T2Space X] in
lemma smoothAntiProjection_star (a : PreL2 A J α hs ht true) :
    smoothAntiProjection A J α hs ht (preStar A J α hs ht a) = smoothAntiProjection A J α hs ht a := by
  apply Subtype.ext
  apply (smoothL2 A J α hs ht true).injective
  change smoothL2 A J α hs ht true (preAntiProjection A J α hs ht (preStar A J α hs ht a)) =
    smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a)
  rw [preAntiProjection_smooth,preAntiProjection_smooth,← l2Star_smooth,l2AntiProjection_star]

omit [T2Space X] in
lemma hodgeSmoothShift_cube_star (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    (hodgeSmoothShift A J α hs ht r^3) (preStar A J α hs ht a) =
      preStar A J α hs ht ((hodgeSmoothShift A J α hs ht r^3) a) := by
  apply (smoothL2 A J α hs ht true).injective
  apply hodgeRegularization_injective A J α hs ht r hr
  rw [hodgeRegularization_smoothShift_cube,
    ← l2Star_smooth A J α hs ht ((hodgeSmoothShift A J α hs ht r^3) a),
    hodgeRegularization_star,hodgeRegularization_smoothShift_cube,l2Star_smooth] <;> exact hr

lemma hodgeCorrectionSource_star
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (a : PreL2 A J α hs ht true) :
    hodgeCorrectionSource A J α hs ht B g μ (preStar A J α hs ht a) =
      hodgeCorrectionSource A J α hs ht B g μ a := by
  change -(unitMeasureCurrent J g μ (B _)) = -(unitMeasureCurrent J g μ (B _))
  rw [smoothAntiProjection_star]

include D hD in
lemma hodgeCorrectionRegularize_star
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (r : ℝ) (hr : 0 < r)
    (hrep : hodgeCubeRepresents A J α hs ht r (hodgeCorrectionSource A J α hs ht B g μ)
      (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr)) :
    l2Star A J α hs ht (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr) =
      hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr := by
  apply hodgeCubeRepresents_unique A J α hs ht D hD r hr _ _ _ _ hrep
  intro a
  rw [l2Star_self_adjoint,l2Star_smooth,← hodgeSmoothShift_cube_star A J α hs ht r hr,
    hrep,hodgeCorrectionSource_star]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

def hodgeCorrectedSource
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] : PreL2 A J α hs ht true →ₗ[ℝ] ℝ :=
by
  let P : PreL2 A J α hs ht true →ₗ[ℝ] ℝ := unitMeasureCurrent J g μ
  exact P+hodgeCorrectionSource A J α hs ht B g μ

omit [MeasurableSpace X] [BorelSpace X] in
lemma hodgeCorrectedSource_annihilates
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (hBc : ∀ f, IsClosed (B f).val)
    (hBR : ∀ f, antiInvariantPart J (B f).val = f.val.val)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J g μ β = 0) (a : PreL2 A J α hs ht true) (hac : IsClosed a.val) :
    hodgeCorrectedSource A J α hs ht B g μ a = 0 :=
  hodgeCorrectionSource_closed A J α hs ht B hBc hBR g μ hann a hac

lemma hodgeCorrected_regularize_represents
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (r : ℝ) (hr : 0 < r)
    (C : HodgeSmoothingCover A J α hs ht D hD r hr)
    (hrep : hodgeCubeRepresents A J α hs ht r (hodgeCorrectionSource A J α hs ht B g μ)
      (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr)) :
    hodgeCubeRepresents A J α hs ht r (hodgeCorrectedSource A J α hs ht B g μ)
      (C.regularize g μ+hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr) := by
  intro a
  rw [inner_add_left,C.regularize_cubeRepresents,hrep]
  rfl

lemma hodgeCorrected_energy_identity
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (hBc : ∀ f, IsClosed (B f).val)
    (hBR : ∀ f, antiInvariantPart J (B f).val = f.val.val)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J g μ β = 0) (r : ℝ) (hr : 0 < r)
    (C : HodgeSmoothingCover A J α hs ht D hD r hr)
    (hrep : hodgeCubeRepresents A J α hs ht r (hodgeCorrectionSource A J α hs ht B g μ)
      (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr)) :
    ⟪C.regularize g μ,l2Star A J α hs ht (C.regularize g μ)⟫ +
      2*⟪C.regularize g μ,hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr⟫+
      ‖hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr‖^2 = 0 := by
  let F := hodgeCorrectedSource A J α hs ht B g μ
  let U := C.regularize g μ
  let V := hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr
  have hUV : hodgeCubeRepresents A J α hs ht r F (U+V) :=
    hodgeCorrected_regularize_represents A J α hs ht D hD B g μ r hr C hrep
  have hF : ∀ a : PreL2 A J α hs ht true, IsClosed a.val → F a = 0 :=
    hodgeCorrectedSource_annihilates A J α hs ht B hBc hBR g μ hann
  have hz := hodge_regularized_zero_pairing A J α hs ht D hD r hr F F (U+V) (U+V)
    hUV hUV hF (fun ξ => hF _ (hodgePreD_closed A J α hs ht ξ))
  have hstar : l2Star A J α hs ht V = V :=
    hodgeCorrectionRegularize_star A J α hs ht D hD B g μ r hr hrep
  have hcross : ⟪V,l2Star A J α hs ht U⟫ = ⟪U,V⟫ := by
    rw [← l2Star_self_adjoint,hstar,real_inner_comm]
  rw [map_add,inner_add_left,inner_add_right,inner_add_right,hstar,hcross,
    real_inner_self_eq_norm_sq] at hz
  change ⟪U,l2Star A J α hs ht U⟫+2*⟪U,V⟫+‖V‖^2 = 0
  linarith
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
