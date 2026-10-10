import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixWeakEquation
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixPartition
import OAI.Geometry.TamingCompatibility.Concentration.HodgeResidualPush

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

def normalCutoff : ContDiffBump (0 : Space) :=
  ⟨D.radius/4,D.radius/2,by linarith [D.radius_pos],by linarith [D.radius_pos]⟩

def normalCompact : Set (Space × Space) :=
  Metric.closedBall (extChartAt Model p p) D.radius ×ˢ Metric.closedBall (0 : Space) D.radius

lemma normalCompact_compact : IsCompact D.normalCompact :=
  (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)

lemma normalCutoff_tsupport : tsupport (D.normalCutoff : Space → ℝ) ⊆ Metric.closedBall (0 : Space) D.radius := by
  rw [D.normalCutoff.tsupport_eq]
  apply Metric.closedBall_subset_closedBall
  change D.radius/2 ≤ D.radius
  linarith [D.radius_pos]

def normalChart : OpenPartialHomeomorph (Space × Space) (Space × Space) :=
  geometricNormalChart D.metricExtension D.frameExtension D.metric_smooth D.frame_smooth
    (extChartAt Model p p) D.centerFrame D.centerFrame_eq

lemma normalCompact_source : D.normalCompact ⊆ D.normalChart.source := fun _ hx => (D.tube hx).1.1.1

def physicalCompact : Set (Space × Space) := D.normalChart '' D.normalCompact

lemma physicalCompact_compact : IsCompact D.physicalCompact :=
  D.normalCompact_compact.image_of_continuousOn (D.normalChart.continuousOn.mono D.normalCompact_source)

lemma physicalCompact_domain : D.physicalCompact ⊆ D.chart.domain ×ˢ D.chart.domain := by
  rintro y ⟨x,hx,rfl⟩
  change x.1 ∈ D.chart.domain ∧ normalMap D.metricExtension D.frameExtension x.1 x.2 ∈ D.chart.domain
  exact ⟨D.actual_subset (D.centers_actual hx.1),D.actual_subset (D.tube hx).2⟩
end ParametrixData

variable [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma coordinatePartition_centerSupport (p : A.centers) :
    tsupport (coordinatePartition A p) ⊆ Metric.closedBall (extChartAt Model p.val p.val) (D p).radius := by
  intro q hq
  obtain ⟨x,hx,rfl⟩ := coordinatePartition_tsupport A p hq
  exact Metric.closedBall_subset_closedBall (by linarith [(D p).radius_pos])
    ((D p).source_image_subset ⟨x,hD p hx,rfl⟩)

include hD in
lemma partition_patch_support (p : A.centers) :
    Function.support (coordinatePartition A p) ×ˢ tsupport ((D p).normalCutoff : Space → ℝ) ⊆
      (D p).normalCompact :=
  Set.prod_mono ((subset_tsupport _).trans (coordinatePartition_centerSupport J α ht A D hD p))
    (D p).normalCutoff_tsupport

def partitionLeading (p : A.centers) (t : ℝ) : Space × Space → W →L[ℝ] W :=
  leadingPatch J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff t

def partitionResidual (p : A.centers) (t : ℝ) : Space × Space → W →L[ℝ] W :=
  residualPatch J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff t

include hD in
lemma partitionLeading_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (y : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => partitionLeading J α ht A D p v.1 v.2) (t,y) :=
  leadingPatch_joint_smooth J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension hs
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff
    (coordinatePartition_smooth_compact A p).1 (D p).normalCutoff.contDiff
    (D p).normalCompact (D p).normalCompact_compact
    ((Set.prod_mono Set.Subset.rfl (subset_tsupport _)).trans (partition_patch_support J α ht A D hD p))
    (D p).actualDomain (D p).tube htp y

include hD in
lemma partitionResidual_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (y : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => partitionResidual J α ht A D p v.1 v.2) (t,y) :=
  residualPatch_joint_smooth J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension hs
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff
    (coordinatePartition_smooth_compact A p).1 (D p).normalCutoff.contDiff
    (D p).normalCompact (D p).normalCompact_compact (partition_patch_support J α ht A D hD p)
    (D p).actualDomain (D p).tube htp y

include hD in
lemma partitionLeading_tsupport (p : A.centers) (t : ℝ) :
    tsupport (partitionLeading J α ht A D p t) ⊆ (D p).physicalCompact := by
  apply KernelExtension.tsupport_push_subset _ _ _ (D p).normalCompact_compact (D p).normalCompact_source
  exact (leadingCoordinate_support J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    _ _ t).trans ((Set.prod_mono Set.Subset.rfl (subset_tsupport _)).trans
      (partition_patch_support J α ht A D hD p))

include hD in
lemma partitionResidual_tsupport (p : A.centers) (t : ℝ) :
    tsupport (partitionResidual J α ht A D p t) ⊆ (D p).physicalCompact := by
  apply KernelExtension.tsupport_push_subset _ _ _ (D p).normalCompact_compact (D p).normalCompact_source
  exact (residualCoordinate_support J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    _ _ t).trans (partition_patch_support J α ht A D hD p)

include hD in
lemma partitionLeading_gaussian (hs : IsSmooth α) (p : A.centers) :
    ∃ L : ℝ, 0 < L ∧ ∀ t : ℝ, 0 < t → ∀ q y : Space,
      ‖partitionLeading J α ht A D p t (q,y)‖ ≤ L^4*FlatHeat.heat (L^2*t) (y-q) :=
  leadingPatch_gaussian J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    (D p).metric_smooth (D p).frame_smooth hs (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff
    (coordinatePartition_bounds A p) (fun _ => ⟨(D p).normalCutoff.nonneg,(D p).normalCutoff.le_one⟩)
    (Metric.closedBall (extChartAt Model p.val p.val) (D p).radius) (isCompact_closedBall _ _)
    ((subset_tsupport _).trans (coordinatePartition_centerSupport J α ht A D hD p))
    (fun _ hq => (D p).actual hq) (D p).radius_pos.le
    ((subset_tsupport _).trans (D p).normalCutoff_tsupport)

include hD in
lemma partitionResidual_gaussian (hs : IsSmooth α) (p : A.centers) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 < L ∧ ∀ t : ℝ, 0 < t → ∀ q y : Space,
      ‖partitionResidual J α ht A D p t (q,y)‖ ≤ M*FlatHeat.heat (L*t) (y-q) :=
  residualPatch_gaussian J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension hs
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff
    (coordinatePartition_bounds A p) (D p).normalCutoff.contDiff (D p).normalCutoff.eventuallyEq_one
    (Metric.closedBall (extChartAt Model p.val p.val) (D p).radius) (isCompact_closedBall _ _)
    ((subset_tsupport _).trans (coordinatePartition_centerSupport J α ht A D hD p))
    (fun _ hq => (D p).actual hq) (D p).radius_pos.le (D p).normalCutoff_tsupport
    (fun _ hx => ((D p).tube hx).1.2)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization NormalJets NormalMetricCalculus
open CoordinateOperator Filter Set MeasureTheory HodgeNormalSymbol
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma ParametrixData.physicalCompact_actual {p : X} (D : ParametrixData J α ht p) :
    D.physicalCompact ⊆ D.actualDomain ×ˢ D.actualDomain := by
  rintro y ⟨z,hz,rfl⟩
  exact ⟨D.centers_actual hz.1,(D.tube hz).2⟩

omit [T2Space X] [CompactSpace X] in
lemma ParametrixData.density_actual {p : X} (D : ParametrixData J α ht p)
    {z : Space} (hz : z ∈ D.actualDomain) :
    volumeDensity (D.metricExtension z) = chartDensity J α p z := by
  rw [D.metric_actual z hz,coordinateMetric_bilinear J α ht p
    (D.chart.domain_subset (D.actual_subset hz))]
  rfl

include hD in
omit [T2Space X] in
lemma partitionLeading_density (p : A.centers) (t : ℝ) (q y : Space) (f : Space → W) :
    chartDensity J α p.val y • (partitionLeading J α ht A D p t (q,y)).adjoint (f y) =
    volumeDensity ((D p).metricExtension y) •
      (partitionLeading J α ht A D p t (q,y)).adjoint (f y) := by
  by_cases hz : partitionLeading J α ht A D p t (q,y) = 0
  · simp [hz]
  · have hm := partitionLeading_tsupport J α ht A D hD p t (subset_tsupport _ hz)
    rw [(D p).density_actual J α ht ((D p).physicalCompact_actual J α ht hm).2]

include hD in
omit [T2Space X] in
lemma partitionLeading_initial (hs : IsSmooth α) (p : A.centers) (q : Space)
    (f : Space → W) (hf : Continuous f) :
    Tendsto (fun t : ℝ => ∫ y : Space, chartDensity J α p.val y •
      (partitionLeading J α ht A D p t (q,y)).adjoint (f y))
      (𝓝[>] 0) (𝓝 (coordinatePartition A p q • f q)) := by
  simp_rw [partitionLeading_density J α ht A D hD]
  have hsub : Function.support (coordinatePartition A p) ×ˢ
      Function.support ((D p).normalCutoff : Space → ℝ) ⊆ (D p).normalChart.source :=
    ((Set.prod_mono Set.Subset.rfl (subset_tsupport _)).trans
      (partition_patch_support J α ht A D hD p)).trans (D p).normalCompact_source
  by_cases hq : coordinatePartition A p q = 0
  · simp_rw [partitionLeading,leadingPatch_change J α ht p.val (D p).chart
      (D p).metricExtension (D p).frameExtension (D p).metric_smooth (D p).frame_smooth
      (extChartAt Model p.val p.val) (D p).centerFrame (D p).centerFrame_eq
      (D p).metric_symmetric (coordinatePartition A p) (D p).normalCutoff hsub]
    simp [hq]
  · exact leadingPatch_initial J α ht p.val (D p).chart (D p).metricExtension
      (D p).frameExtension (D p).metric_smooth (D p).frame_smooth
      (extChartAt Model p.val p.val) (D p).centerFrame (D p).centerFrame_eq hs
      (D p).metric_symmetric ((D p).actual
        (coordinatePartition_centerSupport J α ht A D hD p (subset_tsupport _ hq)))
      (coordinatePartition A p) (D p).normalCutoff (D p).normalCutoff.continuous
      (D p).normalCutoff.hasCompactSupport ((D p).normalCutoff.one_of_mem_closedBall (Metric.mem_closedBall_self (D p).normalCutoff.rIn_pos.le)) hsub f hf

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
