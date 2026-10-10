import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCubeBound

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

lemma hodge_regularized_positive_current_mixing :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (C : HodgeSmoothingCover A J α hs ht D hD r hr)
        (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
        (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ],
        ‖l2AntiProjection A J α hs ht (C.regularize g μ)‖ ≤ B*r*‖C.regularize g μ‖ := by
  obtain ⟨B,hB,hbound⟩ := hodge_relative_antiprojection A J α hs ht D hD
  refine ⟨B,hB,fun r hr hr1 C g μ _ => hbound r hr hr1 _ ?_⟩
  intro a
  rw [C.regularize_smoothShift_cube]
  exact unitMeasureCurrent_antiInvariantPart J g μ a.val a.property
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
include D hD in

lemma hodge_relative_complement :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ U : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪U,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
            (a-preAntiProjection A J α hs ht a))⟫ = 0) →
        ‖U-l2AntiProjection A J α hs ht U‖ ≤ B*r*‖U‖ := by
  obtain ⟨B,hB,hbound⟩ := hodge_cube_commutator_global_bound A J α hs ht D hD
  refine ⟨B,hB,fun r hr hr1 U hU => ?_⟩
  apply norm_le_of_dense_pair_bound _ _ (hodgeSmoothShift_cube_dense A J α hs ht D hD r hr)
    (B*r*‖U‖) (by positivity)
  intro a
  have hz := hU a
  rw [map_sub,map_sub,inner_sub_right,sub_eq_zero] at hz
  have he : ⟪U-l2AntiProjection A J α hs ht U,
      smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)⟫ =
      ⟪U,smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)⟫ := by
    rw [hodgeCubeCommutator_pairing,inner_sub_left,hz]
  calc
    _ = |⟪U,smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)⟫| := by rw [he]
    _ ≤ ‖U‖*‖smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖U‖*(B*r*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)‖) := by
      rw [(smoothL2 A J α hs ht true).norm_map,(smoothL2 A J α hs ht true).norm_map]
      exact mul_le_mul_of_nonneg_left (hbound r hr hr1 a) (norm_nonneg U)
    _ = _ := by ring

omit [T2Space X] in
lemma antiProjection_pair_split (U V : L2 A J α hs ht true) :
    ⟪U,V⟫ = ⟪l2AntiProjection A J α hs ht U,V⟫ +
      ⟪U,V-l2AntiProjection A J α hs ht V⟫ := by
  rw [l2AntiProjection_self_adjoint,inner_sub_right]
  ring
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

lemma hodge_regularized_positive_current_cross :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (C : HodgeSmoothingCover A J α hs ht D hD r hr)
        (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
        (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
        (V : L2 A J α hs ht true),
        (∀ a : PreL2 A J α hs ht true,
          ⟪V,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
            (a-preAntiProjection A J α hs ht a))⟫ = 0) →
        |⟪C.regularize g μ,V⟫| ≤ B*r*‖C.regularize g μ‖*‖V‖ := by
  obtain ⟨B₁,hB₁,h₁⟩ := hodge_regularized_positive_current_mixing A J α hs ht D hD
  obtain ⟨B₂,hB₂,h₂⟩ := hodge_relative_complement A J α hs ht D hD
  refine ⟨B₁+B₂,add_nonneg hB₁ hB₂,fun r hr hr1 C g μ _ V hV => ?_⟩
  let U := C.regularize g μ
  have hb₁ := h₁ r hr hr1 C g μ
  have hb₂ := h₂ r hr hr1 V hV
  change |⟪U,V⟫| ≤ _
  calc
    _ ≤ |⟪l2AntiProjection A J α hs ht U,V⟫| +
        |⟪U,V-l2AntiProjection A J α hs ht V⟫| := by
      rw [antiProjection_pair_split A J α hs ht U V]
      exact abs_add_le _ _
    _ ≤ ‖l2AntiProjection A J α hs ht U‖*‖V‖ +
        ‖U‖*‖V-l2AntiProjection A J α hs ht V‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (B₁*r*‖U‖)*‖V‖ + ‖U‖*(B₂*r*‖V‖) :=
      add_le_add (mul_le_mul_of_nonneg_right hb₁ (norm_nonneg V))
        (mul_le_mul_of_nonneg_left hb₂ (norm_nonneg U))
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
