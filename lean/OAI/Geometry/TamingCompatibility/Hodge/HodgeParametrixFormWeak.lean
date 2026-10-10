import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAtlasPatches

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

def weakSliceDomain (q : Space) : Set Space :=
  (fun z => (q,z)) ⁻¹' parametrixDomain J α ht p E.chart E.metricExtension E.frameExtension
    E.metric_smooth E.frame_smooth (extChartAt Model p p) E.centerFrame E.centerFrame_eq E.actualDomain

lemma weakSliceDomain_open (q : Space) : IsOpen (E.weakSliceDomain q) :=
  (parametrixDomain_open J α ht p E.chart E.metricExtension E.frameExtension E.metric_smooth
    E.frame_smooth (extChartAt Model p p) E.centerFrame E.centerFrame_eq E.actualDomain
    E.actual_open).preimage (continuous_const.prodMk continuous_id)

lemma cutoff_weakSliceDomain {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius) :
    tsupport (E.normalCutoff : Space → ℝ) ⊆ E.weakSliceDomain q :=
  fun _ hz => E.tube ⟨hq,E.normalCutoff_tsupport hz⟩

lemma weakSliceDomain_normal {q z : Space} (hz : z ∈ E.weakSliceDomain q) :
    (q,z) ∈ normalDomain J α ht p E.chart E.metricExtension E.frameExtension := hz.1.2.1

lemma weakSliceDomain_actual {q z : Space} (hz : z ∈ E.weakSliceDomain q) :
    normalMap E.metricExtension E.frameExtension q z ∈ E.actualDomain := hz.2

lemma form_normal_smooth (a : TwoForm X) (ha : IsSmooth a) (q : Space) :
    ContDiffOn ℝ ∞ (HodgeChart.rawVector J α ht p E.chart a ∘
      normalMap E.metricExtension E.frameExtension q) (E.weakSliceDomain q) :=
  (HodgeChart.rawVector_smooth J α ht p E.chart ha).comp
    (normalMap_contDiff E.metricExtension E.frameExtension q).contDiffOn
    (fun _ hz => E.actual_subset (E.weakSliceDomain_actual hz))

lemma cutoff_form_weak_deriv (hs : IsSmooth α) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius)
    {t : ℝ} (htpos : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a) :
    let g := E.metricExtension
    let B := E.frameExtension
    let D := E.chart
    let χ : Space → ℝ := E.normalCutoff
    let η := HodgeChart.rawVector J α ht p D a ∘ normalMap g B q
    HasDerivAt (fun s => ∫ z, normalDensity g B (q,z) * ⟪η z,
      normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫)
      ((∫ z, normalDensity g B (q,z) * ⟪η z,normalGauge J α ht p D g B (q,z)
      (NormalHeatResidual.residual
        (fun y => CutoffFamilies.principal (normalPrincipal g B) χ (q,y))
        (fun y => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (q,y))
        (fun y => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
          (gaugedZero J α ht p D g B) χ (q,y)) t z u)⟫) -
    (∫ z, normalDensity g B (q,z) *
      ⟪differential EuclideanEnergy.e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q) η z,
        differential EuclideanEnergy.e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q)
          (fun y => normalGauge J α ht p D g B (q,y) (χ y • NormalHeatResidual.modelSection t u y)) z⟫)) t := by
  dsimp only
  exact actual_cutoff_weak_deriv J α ht p E.chart E.metricExtension E.frameExtension hs
    E.metric_smooth E.frame_smooth E.metric_symmetric (E.actual hq) E.normalCutoff
    E.normalCutoff.contDiff E.normalCutoff.hasCompactSupport (E.weakSliceDomain_open q)
    (E.cutoff_weakSliceDomain hq) htpos u _ (E.form_normal_smooth a ha q)
    (fun _ hz => E.weakSliceDomain_normal hz)
    (fun _ hz => E.metric_actual _ (E.weakSliceDomain_actual hz))

end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open MeasureTheory
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def leadingSlice (p : A.centers) (q : Space) (t : ℝ) (u : W) : Space → W :=
  fun y => partitionLeading J α ht A E p t (q,y) u

include hE in
lemma leadingSlice_smooth (hs : IsSmooth α) (p : A.centers) (q : Space)
    {t : ℝ} (htp : 0 < t) (u : W) : ContDiff ℝ ∞ (leadingSlice J α ht A E p q t u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  exact ((partitionLeading_smooth J α ht A E hE hs p htp (q,y)).comp y
    (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).clm_apply contDiffAt_const

omit [CompactSpace X] in
lemma leadingSlice_normal (p : A.centers) (q : Space) (t : ℝ) (u : W) {z : Space}
    (hz : (q,z) ∈ (E p).normalChart.source) :
    leadingSlice J α ht A E p q t u (normalMap (E p).metricExtension (E p).frameExtension q z) =
      normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension (q,z)
        ((E p).normalCutoff z • NormalHeatResidual.modelSection t (coordinatePartition A p q • u) z) := by
  unfold leadingSlice partitionLeading
  rw [leadingPatch_apply J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
    (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val) (E p).centerFrame
    (E p).centerFrame_eq (coordinatePartition A p) (E p).normalCutoff t hz]
  simp only [leadingCoordinate,smul_apply,NormalHeatResidual.modelSection,map_smul,smul_smul]
  congr 1
  ring

omit [CompactSpace X] in
lemma leadingSlice_tsupport (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    tsupport (leadingSlice J α ht A E p q t u) ⊆
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
      leadingCoordinate J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
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
  rw [← he,leadingSlice_normal J α ht A E p q t u hz,
    image_eq_zero_of_notMem_tsupport hn]
  simp

omit [CompactSpace X] in
lemma leadingSlice_compact (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    HasCompactSupport (leadingSlice J α ht A E p q t u) :=
  (((E p).normalCutoff.hasCompactSupport).image
    (normalMap_contDiff (E p).metricExtension (E p).frameExtension q).continuous).of_isClosed_subset
      isClosed_closure (leadingSlice_tsupport J α ht A E p q t u)

omit [CompactSpace X] in
lemma leadingSlice_domain (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (t : ℝ) (u : W) : tsupport (leadingSlice J α ht A E p q t u) ⊆ (E p).chart.domain := by
  intro y hy
  obtain ⟨z,hz,rfl⟩ := leadingSlice_tsupport J α ht A E p q t u hy
  have hnormal : z ∈ (E p).weakSliceDomain q := (E p).cutoff_weakSliceDomain hq hz
  exact (E p).actual_subset ((E p).weakSliceDomain_actual hnormal)

omit [CompactSpace X] in
lemma leadingSlice_normal_nhds (p : A.centers) (q : Space) (t : ℝ) (u : W) {z : Space}
    (hz : z ∈ (E p).weakSliceDomain q) :
    (leadingSlice J α ht A E p q t u ∘ normalMap (E p).metricExtension (E p).frameExtension q)
      =ᶠ[𝓝 z] (fun w => normalGauge J α ht p.val (E p).chart
        (E p).metricExtension (E p).frameExtension (q,w)
        ((E p).normalCutoff w • NormalHeatResidual.modelSection t (coordinatePartition A p q • u) w)) := by
  filter_upwards [((E p).weakSliceDomain_open q).mem_nhds hz] with w hw
  exact leadingSlice_normal J α ht A E p q t u hw.1.1.1

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
