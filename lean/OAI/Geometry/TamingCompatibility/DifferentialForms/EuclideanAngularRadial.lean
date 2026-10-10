import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FourthWeightedKernel

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory Filter
open Hermitian UnitaryFrame PlaneVariation Concentration
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

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
lemma euclideanAngularGlobal_nonneg (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ euclideanAngularGlobal A J α hs ht E p uv :=
  indicator_nonneg (fun v _ => euclideanAngularWeight_nonneg A J α hs ht p v) uv

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
lemma euclideanDistanceGlobal_nonneg (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ euclideanDistanceGlobal A J α hs ht E p uv := indicator_nonneg (fun _ _ => norm_nonneg _) uv

omit [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma euclideanAngularGlobal_integrable (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    [IsFiniteMeasure μ] (p : A.centers) : Integrable (euclideanAngularGlobal A J α hs ht E p) (μ.prod μ) := by
  apply (integrable_const (4:ℝ)).mono'
    (euclideanAngularGlobal_measurable A J α hs ht E p).aestronglyMeasurable
  apply ae_of_all
  intro uv
  rw [Real.norm_eq_abs,abs_of_nonneg (euclideanAngularGlobal_nonneg A J α hs ht E p uv)]
  by_cases huv : uv ∈ angularDomain A J α hs ht E p
  · exact (indicator_of_mem huv _).le.trans (euclideanAngularWeight_le A J α hs ht E p huv)
  · simp only [euclideanAngularGlobal,indicator_of_notMem huv]; norm_num

include hE hD in
lemma separating_current_euclidean_radial_angular
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      (∫ uv, euclideanAngularGlobal A J α hs ht E p uv *
        radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv) ∂μ.prod μ) ≤ C ∧
      (∫ uv, euclideanAngularGlobal A J α hs ht E p uv *
        radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv)*
          euclideanDistanceGlobal A J α hs ht E p uv ∂μ.prod μ) ≤ C*r := by
  obtain ⟨C,hC,hbound⟩ := separating_current_euclidean_angular_profile A J α hs ht E hE D hD μ hann p
  refine ⟨8*C,by positivity,fun r hr => ?_⟩
  exact weighted_radial_estimates _ _
    (euclideanAngularGlobal_measurable A J α hs ht E p)
    (euclideanDistanceGlobal_measurable A J α hs ht E p)
    (euclideanAngularGlobal_nonneg A J α hs ht E p)
    (euclideanDistanceGlobal_nonneg A J α hs ht E p)
    (euclideanAngularGlobal_integrable A J α hs ht E μ p) hr (hbound r hr)

include hE hD in
lemma separating_current_euclidean_radial_linear_limit
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    Tendsto (fun r : ℝ => ∫ uv, euclideanAngularGlobal A J α hs ht E p uv *
        radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv)*
          euclideanDistanceGlobal A J α hs ht E p uv ∂μ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,_,hbound⟩ := separating_current_euclidean_radial_angular A J α hs ht E hE D hD μ hann p
  apply squeeze_zero' (Eventually.of_forall fun r => integral_nonneg fun uv => mul_nonneg
    (mul_nonneg (euclideanAngularGlobal_nonneg A J α hs ht E p uv) (radialCoefficient_nonneg _ _))
    (euclideanDistanceGlobal_nonneg A J α hs ht E p uv))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hbound r hr).2
  · simpa only [mul_zero] using tendsto_const_nhds.mul
      (show Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) from nhdsWithin_le_nhds)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
