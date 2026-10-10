import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeRegularization
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothCommutation

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

def unitIntegral
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] : C(MetricUnit g,ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ u, f u ∂μ
      map_add' := fun f k => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (k.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c f }
    (μ.real univ) (fun f => by
      change ‖∫ u, f u ∂μ‖ ≤ μ.real univ*‖f‖
      simpa only [mul_comm] using
        (norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall f.norm_coe_le_norm)))

def hodgePositiveCurrentFamily
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) (r : ℝ) : L2 A J α hs ht true :=
  if hr : 0 < r then (hodgeSmoothingCover A J α hs ht D hD r hr).regularize g μ else 0

lemma hodgePositiveCurrentFamily_pair
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    ⟪hodgePositiveCurrentFamily A J α hs ht D hD g μ r,smoothL2 A J α hs ht true a⟫ =
      unitMeasureCurrent J g μ (hodgeSmoothFamily A J α hs ht D hD r a) := by
  simp only [hodgePositiveCurrentFamily,dite_eq_left hr]
  rw [HodgeSmoothingCover.regularize_pair]
  apply integral_congr_ae
  filter_upwards [] with u
  exact HodgeSmoothingCover.evaluation_smooth _ g u _ _
    (hodgeSmoothFamily_spec A J α hs ht D hD r hr a).symm

lemma hodgePositiveCurrentFamily_tendsto
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (a : PreL2 A J α hs ht true) :
    Tendsto (fun r : ℝ => ⟪hodgePositiveCurrentFamily A J α hs ht D hD g μ r,
      smoothL2 A J α hs ht true a⟫) (𝓝[>] 0) (𝓝 (unitMeasureCurrent J g μ a)) := by
  have hl := (unitIntegral g μ).continuous.tendsto (smoothUnitEvaluation J g a) |>.comp
    (hodgeSmoothFamily_uniform_tendsto A J α hs ht D hD g a)
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hodgePositiveCurrentFamily_pair A J α hs ht D hD g μ r hr a).symm

lemma hodgePositiveCurrentFamily_twice_pair_tendsto
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (a : PreL2 A J α hs ht true) :
    Tendsto (fun r : ℝ => ⟪hodgePositiveCurrentFamily A J α hs ht D hD g μ r,
      hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true a)⟫)
      (𝓝[>] 0) (𝓝 (unitMeasureCurrent J g μ a)) := by
  have hl := (unitIntegral g μ).continuous.tendsto (smoothUnitEvaluation J g a) |>.comp
    (hodgeSmoothFamily_twice_uniform_tendsto A J α hs ht D hD g a)
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [← hodgeSmoothFamily_spec A J α hs ht D hD r hr a,
    hodgePositiveCurrentFamily_pair A J α hs ht D hD g μ r hr]
  rfl

lemma hodgePositiveCurrentFamily_anti_cross_tendsto
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (a : PreL2 A J α hs ht true) :
    Tendsto (fun r : ℝ => ⟪hodgePositiveCurrentFamily A J α hs ht D hD g μ r,
      hodgeRegularization A J α hs ht r
        (smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a))⟫)
      (𝓝[>] 0) (𝓝 0) := by
  have h := hodgePositiveCurrentFamily_twice_pair_tendsto A J α hs ht D hD g μ
    (preAntiProjection A J α hs ht a)
  have he : unitMeasureCurrent J g μ (preAntiProjection A J α hs ht a) = 0 :=
    unitMeasureCurrent_antiInvariantPart J g μ a.val a.property
  rw [he] at h
  exact h

lemma hodgePositiveCurrentFamily_anti_wedge_tendsto
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (a : PreL2 A J α hs ht true) :
    Tendsto (fun r : ℝ => ⟪hodgePositiveCurrentFamily A J α hs ht D hD g μ r,
      l2Star A J α hs ht (hodgeRegularization A J α hs ht r
        (smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a)))⟫)
      (𝓝[>] 0) (𝓝 0) := by
  simp only [← hodgeRegularization_star,preAntiProjection_smooth,l2AntiProjectionStar]
  simpa only [preAntiProjection_smooth] using
    hodgePositiveCurrentFamily_anti_cross_tendsto A J α hs ht D hD g μ a
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma l2AntiProjection_idempotent (a : L2 A J α hs ht true) :
    l2AntiProjection A J α hs ht (l2AntiProjection A J α hs ht a) =
      l2AntiProjection A J α hs ht a := by
  simp only [l2AntiProjection_apply,map_smul,map_sub,l2JAction_square]
  module

lemma smoothAntiProjection_dense (v : L2 A J α hs ht true)
    (hv : l2AntiProjection A J α hs ht v = v) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : PreL2 A J α hs ht true,
      ‖smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a)-v‖ < ε := by
  obtain ⟨a,ha⟩ := (smoothL2_dense A J α hs ht true).exists_dist_lt v hε
  refine ⟨a,?_⟩
  rw [preAntiProjection_smooth,← hv,← map_sub]
  apply (l2AntiProjection_norm A J α hs ht _).trans_lt
  rw [dist_eq_norm,norm_sub_rev] at ha
  simpa only [hv] using ha

lemma smoothAntiProjection_closure :
    closure (range (fun a : PreL2 A J α hs ht true =>
      smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a))) =
      {v : L2 A J α hs ht true | l2AntiProjection A J α hs ht v = v} := by
  apply Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨a,rfl⟩
      change l2AntiProjection A J α hs ht _ = _
      dsimp only
      rw [preAntiProjection_smooth,l2AntiProjection_idempotent]
    · exact isClosed_eq (l2AntiProjection A J α hs ht).continuous continuous_id
  · intro v hv
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨a,ha⟩ := smoothAntiProjection_dense A J α hs ht v hv ε hε
    exact ⟨_,⟨a,rfl⟩,by rw [dist_eq_norm,norm_sub_rev]; exact ha⟩
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
