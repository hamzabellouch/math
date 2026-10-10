import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeTestPairing
import OAI.Geometry.TamingCompatibility.Hodge.HodgeNormalSliceIntegral
import OAI.Geometry.TamingCompatibility.Concentration.HodgeResidualSlices

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

lemma slice_pairing_integral {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius)
    (f k kN : Space → W)
    (hk : Function.support k ⊆ normalMap E.metricExtension E.frameExtension q ''
      tsupport (E.normalCutoff : Space → ℝ))
    (hN : Function.support kN ⊆ tsupport (E.normalCutoff : Space → ℝ))
    (he : ∀ z ∈ E.weakSliceDomain q, k (normalMap E.metricExtension E.frameExtension q z) = kN z) :
    (∫ y, chartDensity J α p y * ⟪f y,k y⟫) =
      ∫ z, normalDensity E.metricExtension E.frameExtension (q,z) *
        ⟪f (normalMap E.metricExtension E.frameExtension q z),kN z⟫ := by
  let F := fun y => ⟪f y,k y⟫
  have hFs : Function.support F ⊆ Function.support k := by
    intro y hy hkzero
    exact hy (by simp only [F,hkzero,inner_zero_right])
  have hd : (∫ y, chartDensity J α p y * F y) =
      ∫ y, volumeDensity (E.metricExtension y) * F y := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : F y = 0
    · simp only [hy,mul_zero]
    · obtain ⟨z,hz,rfl⟩ := hk (hFs hy)
      rw [E.density_actual J α ht (E.weakSliceDomain_actual (E.cutoff_weakSliceDomain hq hz))]
  change (∫ y, chartDensity J α p y * F y) = _
  rw [hd,E.normal_slice_integral hq F (hFs.trans hk)]
  rw [setIntegral_congr_fun (E.weakSliceDomain_open q).measurableSet
    (fun z hz => congrArg (fun w => normalDensity E.metricExtension E.frameExtension (q,z) *
      ⟪f (normalMap E.metricExtension E.frameExtension q z),w⟫) (he z hz))]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hNz : kN z = 0 := Function.notMem_support.mp (fun hh => hz (E.cutoff_weakSliceDomain hq (hN hh)))
  rw [hNz,inner_zero_right,mul_zero]

end ParametrixData
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

lemma leadingSlice_pairing_integral (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (t : ℝ) (u : W) (f : Space → W) :
    (∫ y, chartDensity J α p.val y * ⟪f y,leadingSlice J α ht A E p q t u y⟫) =
    ∫ z, normalDensity (E p).metricExtension (E p).frameExtension (q,z) *
      ⟪f (normalMap (E p).metricExtension (E p).frameExtension q z),
        (E p).cutoffSection q t (coordinatePartition A p q • u) z⟫ :=
  (E p).slice_pairing_integral hq f _ _
    ((subset_tsupport _).trans (leadingSlice_tsupport J α ht A E p q t u))
    ((subset_tsupport _).trans ((E p).cutoffSection_tsupport q t _))
    (fun _ hz => leadingSlice_normal J α ht A E p q t u hz.1.1.1)

lemma residualSlice_pairing_integral (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (t : ℝ) (u : W) (f : Space → W) :
    (∫ y, chartDensity J α p.val y * ⟪f y,residualSlice J α ht A E p q t u y⟫) =
    ∫ z, normalDensity (E p).metricExtension (E p).frameExtension (q,z) *
      ⟪f (normalMap (E p).metricExtension (E p).frameExtension q z),
        (E p).cutoffResidual J α ht q t (coordinatePartition A p q • u) z⟫ := by
  apply (E p).slice_pairing_integral hq f _ _
    ((subset_tsupport _).trans (residualSlice_tsupport J α ht A E p q t u)) _
    (fun _ hz => residualSlice_normal J α ht A E p q t u hz.1.1.1)
  intro z hz
  by_contra hn
  exact hz ((E p).cutoffResidual_zero_off J α ht q t _ hn)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma leadingSlice_weak_deriv (hs : IsSmooth α) (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    {t : ℝ} (htp : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a) :
    HasDerivAt (fun s => ∫ y, chartDensity J α p.val y *
      ⟪HodgeChart.rawVector J α ht p.val (E p).chart a y,leadingSlice J α ht A E p q s u y⟫)
      ((∫ y, chartDensity J α p.val y *
        ⟪HodgeChart.rawVector J α ht p.val (E p).chart a y,residualSlice J α ht A E p q t u y⟫) -
       (∫ y, chartDensity J α p.val y *
        ⟪HodgeChart.normalOperator J α ht p.val (E p).chart (HodgeChart.rawVector J α ht p.val (E p).chart a) y,
          HodgeChart.normalOperator J α ht p.val (E p).chart (leadingSlice J α ht A E p q t u) y⟫)) t := by
  simp only [leadingSlice_pairing_integral J α ht A E p hq,
    residualSlice_pairing_integral J α ht A E p hq,
    leadingSlice_energy_integral J α ht A E hE hs p hq htp u a ha]
  exact (E p).cutoff_form_weak_deriv hs hq htp (coordinatePartition A p q • u) a ha

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def leadingSliceForm (p : A.centers) (q : Space) (t : ℝ) (u : W) : TwoForm X :=
  HodgeChart.manifoldTest J α ht p.val (E p).chart (leadingSlice J α ht A E p q t u)
def residualSliceForm (p : A.centers) (q : Space) (t : ℝ) (u : W) : TwoForm X :=
  HodgeChart.manifoldTest J α ht p.val (E p).chart (residualSlice J α ht A E p q t u)

include hE in
lemma leadingSliceForm_smooth (hs : IsSmooth α) (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    {t : ℝ} (htp : 0 < t) (u : W) : IsSmooth (leadingSliceForm J α ht A E p q t u) := by
  exact HodgeChart.manifoldTest_smooth J α hs ht p.val (E p).chart
    (leadingSlice_smooth J α ht A E hE hs p q htp u)
    (leadingSlice_compact J α ht A E p q t u)
    (leadingSlice_domain J α ht A E p hq t u)

include hE in
lemma residualSliceForm_smooth (hs : IsSmooth α) (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    {t : ℝ} (htp : 0 < t) (u : W) : IsSmooth (residualSliceForm J α ht A E p q t u) := by
  exact HodgeChart.manifoldTest_smooth J α hs ht p.val (E p).chart
    (residualSlice_smooth J α ht A E hE hs p q htp u)
    (residualSlice_compact J α ht A E p q t u)
    (residualSlice_domain J α ht A E p hq t u)

variable [MeasurableSpace X] [BorelSpace X]

include hE in
lemma leadingSliceForm_weak_deriv (hs : IsSmooth α) (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    {t : ℝ} (htp : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a) :
    HasDerivAt (fun s => ∫ x, GeometricAdjoint.pairing J α ht a
        (leadingSliceForm J α ht A E p q s u) x ∂geometricVolume A J α)
      ((∫ x, GeometricAdjoint.pairing J α ht a
        (residualSliceForm J α ht A E p q t u) x ∂geometricVolume A J α) -
       (∫ x, HodgeChart.energyPairing J α ht a
        (leadingSliceForm J α ht A E p q t u) x ∂geometricVolume A J α)) t := by
  unfold residualSliceForm leadingSliceForm
  rw [HodgeChart.pairing_manifoldTest_integral J α ht p.val (E p).chart A hs ha
    (residualSlice_smooth J α ht A E hE hs p q htp u)
    (residualSlice_compact J α ht A E p q t u) (residualSlice_domain J α ht A E p hq t u)]
  rw [HodgeChart.normal_energy_integral J α ht hs p.val (E p).chart A ha
    (leadingSlice_smooth J α ht A E hE hs p q htp u)
    (leadingSlice_compact J α ht A E p q t u) (leadingSlice_domain J α ht A E p hq t u)]
  apply (leadingSlice_weak_deriv J α ht A E hE hs p hq htp u a ha).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds htp] with s hspos
  exact HodgeChart.pairing_manifoldTest_integral J α ht p.val (E p).chart A hs ha
    (leadingSlice_smooth J α ht A E hE hs p q hspos u)
    (leadingSlice_compact J α ht A E p q s u) (leadingSlice_domain J α ht A E p hq s u)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
