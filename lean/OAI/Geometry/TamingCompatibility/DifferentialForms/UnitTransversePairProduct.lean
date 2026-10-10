import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.BoundedMassLimit
import OAI.Geometry.TamingCompatibility.DifferentialForms.EuclideanAngularRadial
import OAI.Geometry.TamingCompatibility.DifferentialForms.UnitTransversePair

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [T2Space X] [CompactSpace X] in
lemma transversePairKernel_nonneg (p : A.centers) (K : Set Space) (r : ℝ) (uv : UnitPair J α hs ht) :
    0 ≤ transversePairKernel A J α hs ht p K r uv := by
  apply indicator_nonneg _ uv
  intro v _
  exact mul_nonneg (mul_nonneg (A.partition.nonneg _ _) (radialCoefficient_nonneg _ _)) (sq_nonneg _)

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [T2Space X] [CompactSpace X] in
lemma transversePairKernel_bound (p : A.centers) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p.val).target) {r : ℝ} (hr : 0 < r) (uv : UnitPair J α hs ht) :
    transversePairKernel A J α hs ht p K r uv ≤ 8/r^2 := by
  by_cases huv : uv ∈ (unitChartDomain J α hs ht p.val K) ×ˢ (unitChartDomain J α hs ht p.val K)
  · rw [transversePairKernel,indicator_of_mem huv]
    have hsrc := (unitChart_mem J α hs ht p.val hKT huv.2).1
    obtain ⟨h₁,h₂,h₃,_⟩ := unitChartPlane J α hs ht p.val uv.2 hsrc
    have ht' := norm_transverse_le (unitChartFirst J α hs ht p.val uv.2)
      (unitChartSecond J α hs ht p.val uv.2)
      (unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1) h₁ h₂ h₃
    have hp : ((1+‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖/r)⁻¹)^6 ≤ 1 := by
      apply pow_le_one₀ (by positivity)
      apply inv_le_one_of_one_le₀
      have : 0 ≤ ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖/r := by positivity
      linarith
    calc
      _ = A.partition p uv.1.val.proj*(radialCoefficient r
          ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖*
          ‖unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.1) uv.2‖^2) := by ring
      _ ≤ radialCoefficient r ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖*
          ‖unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.1) uv.2‖^2 :=
        mul_le_of_le_one_left (mul_nonneg (radialCoefficient_nonneg _ _) (sq_nonneg _)) (A.partition.le_one _ _)
      _ ≤ radialCoefficient r ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖*
          ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht' 2) (radialCoefficient_nonneg _ _)
      _ ≤ (8/r^2)*((1+‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖/r)⁻¹)^6 :=
        radialCoefficient_quadratic_profile hr (norm_nonneg _)
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hp
  · rw [transversePairKernel,indicator_of_notMem huv]
    positivity

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma transversePairKernel_integrable (p : A.centers) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p.val).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : Integrable (transversePairKernel A J α hs ht p K r) (μ.prod μ) := by
  apply (integrable_const (8/r^2)).mono'
    (transversePairKernel_measurable A J α hs ht p hK hKT hr).aestronglyMeasurable
  apply ae_of_all
  intro uv
  rw [Real.norm_eq_abs,abs_of_nonneg (transversePairKernel_nonneg A J α hs ht p K r uv)]
  exact transversePairKernel_bound A J α hs ht p hKT hr uv

lemma separating_probability_transverse_product_limit
    (D : ∀ p : A.centers, Data J α ht p.val)
    (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (p : A.centers) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p.val).target) :
    Tendsto (fun r : ℝ => ∫ uv, transversePairKernel A J α hs ht p K r uv ∂μ.prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply (separating_probability_transverse_pair_limit A J α hs ht D hA μ hann p hK hKT).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (integral_prod _ (transversePairKernel_integrable A J α hs ht p hK hKT μ hr)).symm
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

noncomputable section
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped Topology ENNReal
namespace TamingCompatibility
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integral_sqrt_mul_sqrt_tendsto_eventually {ι : Type*} {l : Filter ι}
    (f g : ι → Ω → ℝ) (hf : ∀ᶠ i in l, Integrable (f i) μ) (hg : ∀ᶠ i in l, Integrable (g i) μ)
    (hfp : ∀ i x, 0 ≤ f i x) (hgp : ∀ i x, 0 ≤ g i x)
    (C : ℝ) (hb : ∀ᶠ i in l, (∫ x, f i x ∂μ) ≤ C)
    (hl : Tendsto (fun i => ∫ x, g i x ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, Real.sqrt (f i x)*Real.sqrt (g i x) ∂μ) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun i => integral_nonneg fun x => by positivity)
  · filter_upwards [hf,hg,hb] with i hi hj hk
    exact (integral_sqrt_mul_sqrt_le (f i) (g i) hi hj (hfp i) (hgp i)).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hk) (Real.sqrt_nonneg _))
  · simpa only [Real.sqrt_zero,mul_zero,Function.comp_def] using
      (tendsto_const_nhds (x := Real.sqrt C)).mul (Real.continuous_sqrt.tendsto 0 |>.comp hl)
end TamingCompatibility

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
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
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE hD hG in
lemma separating_current_angular_transverse_limit
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers)
    {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p.val).target) :
    Tendsto (fun r : ℝ => ∫ uv,
      Real.sqrt (euclideanAngularGlobal A J α hs ht E p uv *
        radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv)) *
      Real.sqrt (transversePairKernel A J α hs ht p K r uv.swap) ∂μ.prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,_,hbound⟩ := separating_current_euclidean_radial_angular A J α hs ht E hE D hD μ hann p
  apply integral_sqrt_mul_sqrt_tendsto_eventually (C := C)
    (fun r uv => euclideanAngularGlobal A J α hs ht E p uv *
      radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv))
    (fun r uv => transversePairKernel A J α hs ht p K r uv.swap)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact weighted_radial_integrable _ _
      (euclideanAngularGlobal_measurable A J α hs ht E p)
      (euclideanDistanceGlobal_measurable A J α hs ht E p)
      (euclideanAngularGlobal_nonneg A J α hs ht E p)
      (euclideanDistanceGlobal_nonneg A J α hs ht E p)
      (euclideanAngularGlobal_integrable A J α hs ht E μ p) hr
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (transversePairKernel_integrable A J α hs ht p hK hKT μ hr).swap
  · exact fun r uv => mul_nonneg (euclideanAngularGlobal_nonneg A J α hs ht E p uv) (radialCoefficient_nonneg _ _)
  · exact fun r uv => transversePairKernel_nonneg A J α hs ht p K r uv.swap
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hbound r hr).1
  · simp_rw [integral_prod_swap]
    exact separating_probability_transverse_product_limit A J α hs ht G hG μ hann p hK hKT
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
