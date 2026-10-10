import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationActivations

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory _root_.OAI.MeasureTheory Filter SummableCutoff
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2
variable (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
  (Q : L2 A J α hs ht true) (S : ConcentrationActivationData A J α hs ht E hE μ Q)

lemma saturation_unit_boundary (θ : smoothForms X 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n N,
    (∫ u : MetricUnit (hermitianMetric J α hs ht),
      |eval (ManifoldForms.wedgeOne (scalarDifferential (saturation S.cutoff n N)) θ.val)
        u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ∂μ) ≤
      ∑ k ∈ Finset.range N, C*stepSize (k+n) := by
  obtain ⟨C,hC,hbound⟩ := S.unit_boundary θ
  refine ⟨C,hC,fun n N => ?_⟩
  calc
    _ ≤ ∫ u : MetricUnit (hermitianMetric J α hs ht), ∑ k ∈ Finset.range N,
        |eval (ManifoldForms.wedgeOne (scalarDifferential (S.cutoff (k+n))) θ.val)
          u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ∂μ :=
      integral_mono (unit_boundary_integrable J α hs ht μ _ (contMDiff_saturation S.smooth n N) θ)
        (integrable_finsetSum _ (fun k _ => unit_boundary_integrable J α hs ht μ _ (S.smooth (k+n)) θ))
        (fun u => saturation_boundary_eval J S.cutoff
          (fun k => (S.smooth k).mdifferentiable (by simp)) S.nonneg θ.val n N u.val.proj u.val.2)
    _ = ∑ k ∈ Finset.range N, ∫ u : MetricUnit (hermitianMetric J α hs ht),
        |eval (ManifoldForms.wedgeOne (scalarDifferential (S.cutoff (k+n))) θ.val)
          u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ∂μ :=
      integral_finsetSum _ (fun k _ => unit_boundary_integrable J α hs ht μ _ (S.smooth (k+n)) θ)
    _ ≤ _ := Finset.sum_le_sum (fun k _ => hbound (k+n))

omit [IsFiniteMeasure μ] in
lemma saturation_Q_boundary (θ : smoothForms X 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n N,
    (∫ x, ‖l2Coefficients A J α hs ht E hE Q x‖ *
      ‖normalizedFrameEncode A J α ht E x
        (ManifoldForms.wedgeOne (scalarDifferential (saturation S.cutoff n N)) θ.val x)‖ ∂geometricVolume A J α) ≤
      ∑ k ∈ Finset.range N, C*stepSize (k+n) := by
  obtain ⟨C,hC,hbound⟩ := S.Q_boundary θ
  refine ⟨C,hC,fun n N => ?_⟩
  calc
    _ ≤ ∫ x, ∑ k ∈ Finset.range N, ‖l2Coefficients A J α hs ht E hE Q x‖ *
        ‖normalizedFrameEncode A J α ht E x
          (ManifoldForms.wedgeOne (scalarDifferential (S.cutoff (k+n))) θ.val x)‖ ∂geometricVolume A J α :=
      integral_mono (coefficient_boundary_integrable A J α hs ht E hE Q _ (contMDiff_saturation S.smooth n N) θ)
        (integrable_finsetSum _ (fun k _ => coefficient_boundary_integrable A J α hs ht E hE Q _ (S.smooth (k+n)) θ))
        (fun x => by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            (saturation_boundary_norm A J α ht E S.cutoff
              (fun k => (S.smooth k).mdifferentiable (by simp)) S.nonneg θ.val n N x) (norm_nonneg _))
    _ = ∑ k ∈ Finset.range N, ∫ x, ‖l2Coefficients A J α hs ht E hE Q x‖ *
        ‖normalizedFrameEncode A J α ht E x
          (ManifoldForms.wedgeOne (scalarDifferential (S.cutoff (k+n))) θ.val x)‖ ∂geometricVolume A J α :=
      integral_finsetSum _ (fun k _ => coefficient_boundary_integrable A J α hs ht E hE Q _ (S.smooth (k+n)) θ)
    _ ≤ _ := Finset.sum_le_sum (fun k _ => hbound (k+n))
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
