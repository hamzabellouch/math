import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCorrectionRegularization
import OAI.Geometry.TamingCompatibility.HeatFlow.ResolventTaylor

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Filter
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

def hodgeCorrectionFamily
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (r : ℝ) : L2 A J α hs ht true :=
  if hr : 0 < r then hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr else 0

theorem exists_convergent_closed_lift
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    ∃ B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2,
      (∀ f, IsClosed (B f).val) ∧
      (∀ f, antiInvariantPart J (B f).val = f.val.val) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ],
        (∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
          hodgeCubeRepresents A J α hs ht r (hodgeCorrectionSource A J α hs ht B g μ)
            (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr) ∧
          ‖hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr‖ ≤ μ.real univ*C*(r⁻¹)^3) ∧
        ∀ a : PreL2 A J α hs ht true,
          Tendsto (fun r : ℝ => ⟪hodgeCorrectionFamily A J α hs ht D hD B g μ r,
            smoothL2 A J α hs ht true a⟫) (𝓝[>] 0) (𝓝 (hodgeCorrectionSource A J α hs ht B g μ a)) := by
  obtain ⟨B,hBc,hBR,C,hC,hB⟩ := exists_regularizable_closed_lift A J α hs ht D hD g
  refine ⟨B,hBc,hBR,C,hC,fun μ _ => ⟨hB μ,fun a => ?_⟩⟩
  apply ResolventTaylor.cube_distribution_tendsto (hodgeLaplacian A J α hs ht)
    (smoothL2 A J α hs ht true).toLinearMap
    (hodgeCorrectionSource A J α hs ht B g μ)
    (hodgeCorrectionFamily A J α hs ht D hD B g μ) (μ.real univ*C)
  · intro r hr hr1
    simpa only [hodgeCorrectionFamily,dite_eq_left hr] using (hB μ r hr hr1).2
  · intro r hr hr1 b
    simpa only [hodgeCorrectionFamily,dite_eq_left hr,hodgeSmoothShift,LinearIsometry.coe_toLinearMap] using
      (hB μ r hr hr1).1 b
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricHilbert
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel unitT2

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitMeasureCurrent_taming_normalized
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] :
    unitMeasureCurrent J (hermitianMetric J α hs ht) μ ⟨α,hs⟩ = 1 := by
  calc
    _ = unitMeasureCurrent J (hermitianMetric J α hs ht) μ
      ⟨invariantPart J α,hs.invariantPart J⟩ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u =>
          (eval_invariantPart_complexLine J α u.val.proj u.val.2).symm)
    _ = 1 := unitMeasureCurrent_normalized J α hs ht μ

namespace GeometricHilbert
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [MeasurableSpace X] [BorelSpace X] in

lemma hodgeCorrectionSource_eq
    (B B' : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (hBc : ∀ f, IsClosed (B f).val)
    (hBR : ∀ f, antiInvariantPart J (B f).val = f.val.val)
    (hBc' : ∀ f, IsClosed (B' f).val)
    (hBR' : ∀ f, antiInvariantPart J (B' f).val = f.val.val)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J g μ β = 0) :
    hodgeCorrectionSource A J α hs ht B g μ = hodgeCorrectionSource A J α hs ht B' g μ := by
  ext a
  let f := smoothAntiProjection A J α hs ht a
  have he : smoothAntiProjection A J α hs ht (B' f) = f := by
    apply Subtype.ext
    apply Subtype.ext
    exact hBR' f
  have hz := hodgeCorrectionSource_closed A J α hs ht B hBc hBR g μ hann (B' f) (hBc' f)
  change unitMeasureCurrent J g μ (B' f) -
    unitMeasureCurrent J g μ (B (smoothAntiProjection A J α hs ht (B' f))) = 0 at hz
  rw [he] at hz
  change -(unitMeasureCurrent J g μ (B f)) = -(unitMeasureCurrent J g μ (B' f))
  linarith

omit [MeasurableSpace X] [BorelSpace X] in

lemma hodgeCorrectionSource_taming
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (hBc : ∀ f, IsClosed (B f).val)
    (hBR : ∀ f, antiInvariantPart J (B f).val = f.val.val)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (hc : IsClosed α) :
    hodgeCorrectionSource A J α hs ht B (hermitianMetric J α hs ht) μ ⟨α,hs⟩ = -1 := by
  have hz := hodgeCorrectionSource_closed A J α hs ht B hBc hBR
    (hermitianMetric J α hs ht) μ hann ⟨α,hs⟩ hc
  rw [unitMeasureCurrent_taming_normalized J α hs ht μ] at hz
  linarith
end GeometricHilbert
end TamingCompatibility

end
end

end
end

end OAI
