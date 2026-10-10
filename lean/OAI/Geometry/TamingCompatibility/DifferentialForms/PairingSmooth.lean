import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexEquiv

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.GeometricAdjoint
open Bundle ManifoldForms ManifoldHodge ManifoldTop
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
lemma pairing_one_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a b : ManifoldForms.Form X 1}
    (ha : Smooth a) (hb : Smooth b) : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (pairing J α ht a b) := by
  apply scalar_smooth_of_charts
  intro p
  apply (SmoothMetric.contDiffOn_pairing_one (coordinateMetric J α ht p) (coordinateJ J p)
    (by simp [Space]) (isOpen_extChartAt_target p) (coordinateMetric_smooth J α hs ht p)
    (coordinateJ_smooth J p) (fun z hz => coordinateJ_square J p hz)
    (fun z hz => coordinateMetric_hermitian J α ht p hz)
    (smooth_chart a ha p) (smooth_chart b hb p)).congr
  intro z hz
  let L : Space ≃L[ℝ] Space := inverseChartEquiv p z hz
  have hL : L.toContinuousLinearMap = mfderiv Model Model (extChartAt Model p).symm z :=
    inverseChartEquiv_coe p z hz
  have he := MetricForms.pairing_one_comp (E := Space) (D := Space) (coordinateMetric J α ht p z)
    (pointMetric J α ht ((extChartAt Model p).symm z)) L
    (coordinateMetric_pullback J α ht p hz) (by simp [Space]) (a ((extChartAt Model p).symm z)) (b ((extChartAt Model p).symm z))
  rw [hL] at he
  exact he.symm
lemma pairing_two_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a b : ManifoldForms.Form X 2}
    (ha : Smooth a) (hb : Smooth b) : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (pairing J α ht a b) := by
  apply scalar_smooth_of_charts
  intro p
  apply (SmoothMetric.contDiffOn_pairing_two (coordinateMetric J α ht p) (coordinateJ J p)
    (by simp [Space]) (isOpen_extChartAt_target p) (coordinateMetric_smooth J α hs ht p)
    (coordinateJ_smooth J p) (fun z hz => coordinateJ_square J p hz)
    (fun z hz => coordinateMetric_hermitian J α ht p hz)
    (smooth_chart a ha p) (smooth_chart b hb p)).congr
  intro z hz
  let L : Space ≃L[ℝ] Space := inverseChartEquiv p z hz
  have hL : L.toContinuousLinearMap = mfderiv Model Model (extChartAt Model p).symm z :=
    inverseChartEquiv_coe p z hz
  have he := MetricForms.pairing_two_comp (E := Space) (D := Space) (coordinateMetric J α ht p z)
    (pointMetric J α ht ((extChartAt Model p).symm z)) L
    (coordinateMetric_pullback J α ht p hz) (by simp [Space]) (a ((extChartAt Model p).symm z)) (b ((extChartAt Model p).symm z))
  rw [hL] at he
  exact he.symm
end TamingCompatibility.GeometricAdjoint

namespace TamingCompatibility.ManifoldVolume
open Bundle MeasureTheory ManifoldLocalization
open scoped Topology Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X)

theorem geometricVolume_openPos (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) : (geometricVolume A J α).IsOpenPosMeasure := by
  classical
  constructor
  intro U hU hne
  obtain ⟨x,hxU⟩ := hne
  have hn : (∑ p : A.centers, A.partition p x) ≠ 0 := by
    rw [partition_sum A x]
    exact one_ne_zero
  obtain ⟨p,_,hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hp' : 0 < A.partition p x := lt_of_le_of_ne (A.partition.nonneg _ _) hp.symm
  let e := extChartAt Model p.val
  have hx : x ∈ e.source := A.subordinate p (subset_tsupport _ hp)
  have hz : e x ∈ e.target := e.map_source hx
  let w := chartWeight A J α p
  have hw : Continuous w := (chartWeight_smooth_compact A J α hs ht p).1.continuous
  have hwz : 0 < w (e x) := by
    change 0 < e.target.indicator (fun z => A.partition p (e.symm z) * chartDensity J α p.val z) (e x)
    rw [Set.indicator_of_mem hz,e.left_inv hx]
    exact mul_pos hp' (chartDensity_pos J α ht p.val hz)
  let V : Set Space := (e.target ∩ e.symm ⁻¹' U) ∩ {z | 0 < w z}
  have hV : IsOpen V :=
    ((continuousOn_extChartAt_symm p.val).isOpen_inter_preimage
      (isOpen_extChartAt_target p.val) hU).inter (isOpen_lt continuous_const hw)
  have hzV : e x ∈ V := ⟨⟨hz,by simpa only [Set.mem_preimage,e.left_inv hx] using hxU⟩,hwz⟩
  have hVm : 0 < volume V := hV.measure_pos volume ⟨e x,hzV⟩
  let f := fun z => ENNReal.ofReal (w z)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp hw.measurable
  have hVF : V ⊆ Function.support f ∩ chartInverse p.val ⁻¹' U := by
    intro z hz
    refine ⟨?_,?_⟩
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr hz.2)
    · change (if z ∈ e.target then e.symm z else p.val) ∈ U
      rw [ite_eq_left hz.1.1]
      exact hz.1.2
  have hpos : 0 < chartMeasure A J α p U := by
    rw [chartMeasure,Measure.map_apply (chartInverse_measurable p.val) hU.measurableSet,
      withDensity_apply _ ((chartInverse_measurable p.val) hU.measurableSet)]
    exact (setLIntegral_pos_iff hf).mpr (lt_of_lt_of_le hVm (measure_mono hVF))
  have hle : chartMeasure A J α p U ≤ geometricVolume A J α U := by
    rw [geometricVolume,Measure.finsetSum_apply]
    exact Finset.single_le_sum (fun q _ => show (0 : ENNReal) ≤ chartMeasure A J α q U from bot_le) (Finset.mem_univ p)
  exact ne_of_gt (lt_of_lt_of_le hpos hle)
end TamingCompatibility.ManifoldVolume

namespace TamingCompatibility.GeometricAdjoint
open MeasureTheory ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X)

include A in

theorem rdd_kernel_closed (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a : TwoForm X} (ha : IsSmooth a)
    (hRa : antiInvariantPart J a = a) (hker : rdd J α ht a = 0) : IsClosed a := by
  let := geometricVolume_finite A J α hs ht
  let := geometricVolume_openPos A J α hs ht
  let c := codifferential J α ht a
  have hc : Smooth c := codifferential_smooth J α hs ht ha
  have hcont : Continuous (pairing J α ht c c) := (pairing_one_smooth J α hs ht hc hc).continuous
  have hnonneg : 0 ≤ pairing J α ht c c := fun x =>
    MetricForms.pairing_self_nonneg (pointMetric J α ht x) _
  have hi : Integrable (pairing J α ht c c) (geometricVolume A J α) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg := rdd_green A J α hs ht ha ha hRa
  have hz : pairing J α ht (rdd J α ht a) a = 0 := by
    rw [hker]
    funext x
    change MetricForms.pairing (pointMetric J α ht x) 0 (a x) = 0
    have hzero : (0 : MetricForms.Form Space 2).compContinuousLinearMap
        (MetricModel.equiv (pointMetric J α ht x)).toContinuousLinearMap = 0 := by ext v; rfl
    simp only [MetricForms.pairing,hzero,FormMetric.pairing,_root_.map_zero,inner_zero_left]
  simp only [hz,Pi.zero_apply,integral_zero] at hg
  have he : pairing J α ht c c = 0 :=
    Measure.eq_of_ae_eq ((integral_eq_zero_iff_of_nonneg hnonneg hi).mp hg.symm) hcont continuous_zero
  apply coclosed_antiInvariant_closed J α ht ha hRa
  funext x
  apply (MetricForms.pairing_self_eq_zero (pointMetric J α ht x) (c x)).mp
  exact congrFun he x
end TamingCompatibility.GeometricAdjoint

end

end OAI
