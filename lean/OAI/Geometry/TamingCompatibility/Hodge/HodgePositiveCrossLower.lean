import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAngularPoint
import OAI.Geometry.TamingCompatibility.DifferentialForms.PhysicalUnitProfile

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma regularize_positive_cross_lower_of_point
    (μ ν : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr)
    (C B : ℝ)
    (hb : ∀ v u : MetricUnit (hermitianMetric J α hs ht),
      -C*(physicalProfile J α hs ht r v.val.proj u.val.proj/r^2)-B*r^2 ≤
        S.wedgeKernel (hermitianMetric J α hs ht) v u) :
    -C*(∫ v, physicalProfileMass J α hs ht μ r v.val.proj/r^2 ∂ν)-B*r^2*ν.real univ ≤
      ⟪S.regularize (hermitianMetric J α hs ht) μ,
        l2Star A J α hs ht (S.regularize (hermitianMetric J α hs ht) ν)⟫ := by
  have hc := physicalProfile_unit_pair_continuous J α hs ht hr
  have hh := continuous_double_integral_lower ν μ
    (fun vu : MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht) => physicalProfile J α hs ht r vu.1.val.proj vu.2.val.proj/r^2)
    (fun vu => S.wedgeKernel (hermitianMetric J α hs ht) vu.1 vu.2) (hc.div_const _) (S.wedgeKernel_continuous (hermitianMetric J α hs ht)) C (B*r^2) hb
  simp_rw [integral_div] at hh
  rw [← S.regularize_wedge (hermitianMetric J α hs ht) ν μ] at hh
  rw [← l2Star_self_adjoint,real_inner_comm] at hh
  simpa only [physicalProfileMass,integral_div] using hh

include hE in
lemma same_resolvent_positive_cross_lower :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (μ ν : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] [IsFiniteMeasure ν],
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr),
      -C*(∫ v, physicalProfileMass J α hs ht μ r v.val.proj/r^2 ∂ν)-B*r^2*ν.real univ ≤
        ⟪S.regularize (hermitianMetric J α hs ht) μ,
          l2Star A J α hs ht (S.regularize (hermitianMetric J α hs ht) ν)⟫ := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_wedge_point_lower A J α hs ht E hE D hD 6 1
  refine ⟨C,B,hC,hB,fun μ ν _ _ r hr S => ?_⟩
  apply regularize_positive_cross_lower_of_point A J α hs ht D hD μ ν r hr S C B
  intro v u
  have hh := hbound r hr S v u
  change -(C/r^2)*physicalProfile J α hs ht r v.val.proj u.val.proj-B*r^2 ≤ _ at hh
  convert hh using 1; ring
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
