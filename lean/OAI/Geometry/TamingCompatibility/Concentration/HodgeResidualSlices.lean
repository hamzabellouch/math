import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixFormWeak

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open MeasureTheory
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance residualSlicesMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance residualSlicesMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] in

def ParametrixData.cutoffResidual {p : X} (D : ParametrixData J α ht p)
    (q : Space) (t : ℝ) (u : W) : Space → W := fun z =>
  normalGauge J α ht p D.chart D.metricExtension D.frameExtension (q,z)
    (NormalHeatResidual.residual
      (fun y => CutoffFamilies.principal (normalPrincipal D.metricExtension D.frameExtension)
        D.normalCutoff (q,y))
      (fun y => CutoffFamilies.first (normalPrincipal D.metricExtension D.frameExtension)
        (gaugedFirst J α ht p D.chart D.metricExtension D.frameExtension) D.normalCutoff (q,y))
      (fun y => CutoffFamilies.zero (normalPrincipal D.metricExtension D.frameExtension)
        (gaugedFirst J α ht p D.chart D.metricExtension D.frameExtension)
        (gaugedZero J α ht p D.chart D.metricExtension D.frameExtension) D.normalCutoff (q,y)) t z u)

omit [CompactSpace X] in
lemma ParametrixData.cutoffResidual_zero_off {p : X} (D : ParametrixData J α ht p)
    (q : Space) (t : ℝ) (u : W) {z : Space} (hz : z ∉ tsupport (D.normalCutoff : Space → ℝ)) :
    D.cutoffResidual J α ht q t u z = 0 := by
  rw [ParametrixData.cutoffResidual,CutoffFamilies.residual_zero_off _ _ _ D.normalCutoff q t hz]
  simp only [zero_apply,map_zero]

def residualSlice (p : A.centers) (q : Space) (t : ℝ) (u : W) : Space → W :=
  fun y => partitionResidual J α ht A E p t (q,y) u

include hE in
lemma residualSlice_smooth (hs : IsSmooth α) (p : A.centers) (q : Space)
    {t : ℝ} (htp : 0 < t) (u : W) : ContDiff ℝ ∞ (residualSlice J α ht A E p q t u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  exact ((partitionResidual_smooth J α ht A E hE hs p htp (q,y)).comp y
    (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).clm_apply contDiffAt_const

omit [CompactSpace X] in
lemma residualSlice_normal (p : A.centers) (q : Space) (t : ℝ) (u : W) {z : Space}
    (hz : (q,z) ∈ (E p).normalChart.source) :
    residualSlice J α ht A E p q t u (normalMap (E p).metricExtension (E p).frameExtension q z) =
      (E p).cutoffResidual J α ht q t (coordinatePartition A p q • u) z := by
  unfold residualSlice partitionResidual
  rw [residualPatch_apply J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
    (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val) (E p).centerFrame
    (E p).centerFrame_eq (coordinatePartition A p) (E p).normalCutoff t hz]
  simp only [residualCoordinate,ParametrixData.cutoffResidual,smul_apply,
    ContinuousLinearMap.comp_apply,map_smul]

omit [CompactSpace X] in
lemma residualSlice_tsupport (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    tsupport (residualSlice J α ht A E p q t u) ⊆
      normalMap (E p).metricExtension (E p).frameExtension q ''
        tsupport ((E p).normalCutoff : Space → ℝ) := by
  classical
  apply closure_minimal _
    (((E p).normalCutoff.hasCompactSupport).image
      (normalMap_contDiff (E p).metricExtension (E p).frameExtension q).continuous).isClosed
  intro y hy
  have htarget : (q,y) ∈ (E p).normalChart.target := by
    by_contra hn
    apply hy
    change (if (q,y) ∈ (E p).normalChart.target then
      residualCoordinate J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
        (coordinatePartition A p) (E p).normalCutoff t ((E p).normalChart.symm (q,y)) else 0) u = 0
    rw [ite_eq_right hn,zero_apply]
  let z := ((E p).normalChart.symm (q,y)).2
  have hf : ((E p).normalChart.symm (q,y)).1 = q :=
    geometricNormalChart_symm_fst (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq htarget
  have hz : (q,z) ∈ (E p).normalChart.source := by
    have heq : (q,z) = (E p).normalChart.symm (q,y) := Prod.ext hf.symm rfl
    rw [heq]
    exact (E p).normalChart.map_target htarget
  have he : normalMap (E p).metricExtension (E p).frameExtension q z = y :=
    geometricNormalChart_symm_right (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq htarget
  refine ⟨z,?_,he⟩
  by_contra hn
  apply hy
  rw [← he,residualSlice_normal J α ht A E p q t u hz,
    (E p).cutoffResidual_zero_off J α ht q t _ hn]

omit [CompactSpace X] in
lemma residualSlice_compact (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    HasCompactSupport (residualSlice J α ht A E p q t u) :=
  (((E p).normalCutoff.hasCompactSupport).image
    (normalMap_contDiff (E p).metricExtension (E p).frameExtension q).continuous).of_isClosed_subset
      isClosed_closure (residualSlice_tsupport J α ht A E p q t u)

omit [CompactSpace X] in
lemma residualSlice_domain (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (t : ℝ) (u : W) : tsupport (residualSlice J α ht A E p q t u) ⊆ (E p).chart.domain := by
  intro y hy
  obtain ⟨z,hz,rfl⟩ := residualSlice_tsupport J α ht A E p q t u hy
  have hnormal : z ∈ (E p).weakSliceDomain q := (E p).cutoff_weakSliceDomain hq hz
  exact (E p).actual_subset ((E p).weakSliceDomain_actual hnormal)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
