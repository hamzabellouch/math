import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.UnitTransversePairProduct
import OAI.Geometry.TamingCompatibility.DifferentialForms.SecondVariationIntegral

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE hD hG in
lemma separating_current_second_variation_limit
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    Tendsto (fun r : ℝ => ∫ uv, secondVariationDensity A J α hs ht E p r uv ∂μ.prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨P,C,hP,hC,hbound⟩ := secondVariationDensity_bound A J α hs ht E hE p
  let w := euclideanAngularGlobal A J α hs ht E p
  let d := euclideanDistanceGlobal A J α hs ht E p
  let f := fun r uv => w uv*radialCoefficient r (d uv)*d uv
  let g := fun r uv => Real.sqrt (w uv*radialCoefficient r (d uv))*
    Real.sqrt (transversePairKernel A J α hs ht p (E p).concentrationCompact r uv.swap)
  have hi (r : ℝ) (hr : 0 < r) : Integrable (f r) (μ.prod μ) :=
    weighted_radial_linear_integrable w d (euclideanAngularGlobal_measurable A J α hs ht E p)
      (euclideanDistanceGlobal_measurable A J α hs ht E p)
      (euclideanAngularGlobal_nonneg A J α hs ht E p) (euclideanDistanceGlobal_nonneg A J α hs ht E p)
      (euclideanAngularGlobal_integrable A J α hs ht E μ p) hr
  have hj (r : ℝ) (hr : 0 < r) : Integrable (g r) (μ.prod μ) := by
    have ha := sqrt_memLp_two (fun uv => w uv*radialCoefficient r (d uv))
      (weighted_radial_integrable w d (euclideanAngularGlobal_measurable A J α hs ht E p)
        (euclideanDistanceGlobal_measurable A J α hs ht E p)
        (euclideanAngularGlobal_nonneg A J α hs ht E p) (euclideanDistanceGlobal_nonneg A J α hs ht E p)
        (euclideanAngularGlobal_integrable A J α hs ht E μ p) hr)
      (fun uv => mul_nonneg (euclideanAngularGlobal_nonneg A J α hs ht E p uv) (radialCoefficient_nonneg _ _))
    have hb := sqrt_memLp_two (fun uv : UnitPair J α hs ht => transversePairKernel A J α hs ht p (E p).concentrationCompact r uv.swap)
      ((transversePairKernel_integrable A J α hs ht p (E p).concentrationCompact_compact
        (E p).concentrationCompact_target μ hr).swap)
      (fun uv => transversePairKernel_nonneg A J α hs ht p (E p).concentrationCompact r uv.swap)
    exact ha.integrable_mul hb
  have hf : Tendsto (fun r : ℝ => ∫ uv, f r uv ∂μ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    separating_current_euclidean_radial_linear_limit A J α hs ht E hE D hD μ hann p
  have hg : Tendsto (fun r : ℝ => ∫ uv, g r uv ∂μ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    separating_current_angular_transverse_limit A J α hs ht E hE D hD G hG μ hann p
      (E p).concentrationCompact_compact (E p).concentrationCompact_target
  apply squeeze_zero' (g := fun r => 15*P*(∫ uv, f r uv ∂μ.prod μ)+
    6*P*(∫ uv, g r uv ∂μ.prod μ)+C*r^4) (Eventually.of_forall fun r => integral_nonneg
    (secondVariationDensity_nonneg A J α hs ht E p r))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hb := integral_mono (secondVariationDensity_integrable A J α hs ht E hE μ p hr)
      (((hi r hr).const_mul (15*P)).add ((hj r hr).const_mul (6*P)) |>.add (integrable_const (C*r^4)))
      (hbound r hr)
    simp only [Pi.add_apply] at hb
    have hab : Integrable (fun uv => 15*P*f r uv+6*P*g r uv) (μ.prod μ) :=
      ((hi r hr).const_mul _).add ((hj r hr).const_mul _)
    have ha : Integrable (fun uv => 15*P*f r uv) (μ.prod μ) := (hi r hr).const_mul _
    have hb' : Integrable (fun uv => 6*P*g r uv) (μ.prod μ) := (hj r hr).const_mul _
    rw [integral_add hab (integrable_const _), integral_add ha hb',
      integral_const_mul,integral_const_mul] at hb
    simpa only [integral_const,probReal_univ,one_smul] using hb
  · have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [mul_zero,add_zero,zero_pow (by decide : (4:ℕ) ≠ 0)] using
      ((hf.const_mul (15*P)).add (hg.const_mul (6*P))).add ((hr.pow 4).const_mul C)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
