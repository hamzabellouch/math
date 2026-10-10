import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixLocalWeak
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCompactTimeIntegral

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
local instance parametrixWeakEquationMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance parametrixWeakEquationMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

lemma actual_cutoff_weak_deriv (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ y v w, g y v w = g y w v) {q : Space}
    (hactual : ActualData J α ht p D q g B)
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    {U : Set Space} (hU : IsOpen U) (hχU : tsupport χ ⊆ U)
    {t : ℝ} (htpos : 0 < t) (u : W)
    (η : Space → W) (hη : ContDiffOn ℝ ∞ η U)
    (hsub : ∀ z ∈ U, (q,z) ∈ normalDomain J α ht p D g B)
    (hgact : ∀ z ∈ U,
      g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear) :
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
  have hi := actual_cutoff_time_integral_local J α ht p D g B hg hB q χ hχ.continuous
    hχc hU hχU htpos u η hη
  have he := actual_cutoff_weak_local J α ht p D g B hs hg hB hsym hactual χ hχ hχc
    hU hχU htpos u η hη hsub hgact
  convert hi using 1
  exact (eq_sub_of_add_eq he).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance parametrixDataMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance parametrixDataMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

structure ParametrixData (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) (p : X) where
  chart : GeometricChart.Data J α ht p
  metricExtension : Space → MetricTensor (V := Space)
  frameExtension : Space → Space →L[ℝ] Space
  metric_smooth : ContDiff ℝ ∞ metricExtension
  frame_smooth : ContDiff ℝ ∞ frameExtension
  actualDomain : Set Space
  actual_open : IsOpen actualDomain
  actual_center : extChartAt Model p p ∈ actualDomain
  actual_subset : actualDomain ⊆ chart.domain
  metric_actual : ∀ y ∈ actualDomain, metricExtension y = (coordinateMetric J α ht p y).bilinear
  frame_actual : ∀ y ∈ actualDomain, frameExtension y = frameMap (fun i => chart.frame i y)
  metric_symmetric : ∀ y v w, metricExtension y v w = metricExtension y w v
  centerFrame : Space ≃L[ℝ] Space
  centerFrame_eq : frameExtension (extChartAt Model p p) = centerFrame
  radius : ℝ
  radius_pos : 0 < radius
  tube : Metric.closedBall (extChartAt Model p p) radius ×ˢ Metric.closedBall (0 : Space) radius ⊆
    parametrixDomain J α ht p chart metricExtension frameExtension metric_smooth frame_smooth
      (extChartAt Model p p) centerFrame centerFrame_eq actualDomain

lemma parametrixData_nonempty (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) : Nonempty (ParametrixData J α ht p) := by
  let D := GeometricChart.data J α hs ht p
  let q := extChartAt Model p p
  have hq : q ∈ D.domain := D.ball_subset (Metric.mem_closedBall_self (by linarith [D.radius_pos]))
  obtain ⟨g,B,O,hg,hB,hO,hqO,hOD,hga,hBa,hgs⟩ :=
    exists_metric_frame_extension J α hs ht p D hq
  let Bq := frameEquiv (coordinateMetric J α ht p q) (fun i => D.frame i q) (D.frame_gram q hq)
  have hBq : B q = Bq := (hBa q hqO).trans rfl
  have hact : ActualData J α ht p D q g B := ⟨O,hO,hqO,hOD,hga,hBa,hgs⟩
  obtain ⟨r,hr,htube⟩ := exists_parametrix_tube J α ht p D g B hg hB q Bq hBq O hO hqO hact
  exact ⟨⟨D,g,B,hg,hB,O,hO,hqO,hOD,hga,hBa,hgs,Bq,hBq,r,hr,htube⟩⟩

def parametrixData (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) : ParametrixData J α ht p :=
  Classical.choice (parametrixData_nonempty J α hs ht p)

namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

def source : Set X := (extChartAt Model p).source ∩
  (extChartAt Model p) ⁻¹' Metric.ball (extChartAt Model p p) (D.radius/2)

lemma source_open : IsOpen D.source :=
  (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p) Metric.isOpen_ball

lemma mem_source : p ∈ D.source :=
  ⟨mem_extChartAt_source p,Metric.mem_ball_self (half_pos D.radius_pos)⟩

lemma source_subset : D.source ⊆ (extChartAt Model p).source := Set.inter_subset_left

lemma centers_actual : Metric.closedBall (extChartAt Model p p) D.radius ⊆ D.actualDomain := by
  intro q hq
  have hh := (D.tube (show (q,0) ∈ Metric.closedBall (extChartAt Model p p) D.radius ×ˢ
      Metric.closedBall (0 : Space) D.radius from
        ⟨hq,Metric.mem_closedBall_self D.radius_pos.le⟩)).2
  simpa only [Set.mem_preimage,normalMap_zero] using hh

lemma actual {q : Space} (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius) :
    ActualData J α ht p D.chart q D.metricExtension D.frameExtension :=
  ⟨D.actualDomain,D.actual_open,D.centers_actual hq,D.actual_subset,
    D.metric_actual,D.frame_actual,D.metric_symmetric⟩

lemma source_image_subset : (extChartAt Model p) '' D.source ⊆
    Metric.closedBall (extChartAt Model p p) (D.radius/2) := by
  rintro q ⟨y,hy,rfl⟩
  exact Metric.ball_subset_closedBall hy.2

end ParametrixData

theorem finite_parametrix_partition [T2Space X] [CompactSpace X]
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J) :
    ∃ A : FiniteCharts X, ∀ p : A.centers,
      tsupport (A.partition p) ⊆ (parametrixData J α hs ht p.val).source := by
  classical
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover
    (fun p : X => (parametrixData J α hs ht p).source)
    (fun p => (parametrixData J α hs ht p).source_open)
    (fun p _ => mem_iUnion_of_mem p (parametrixData J α hs ht p).mem_source)
  have hc : (univ : Set X) ⊆ ⋃ p : s, (parametrixData J α hs ht p.val).source := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => (parametrixData J α hs ht p.val).source)
    (fun p => (parametrixData J α hs ht p.val).source_open) hc
  refine ⟨⟨s,ρ,fun p => (hρ p).trans (parametrixData J α hs ht p.val).source_subset⟩,?_⟩
  exact hρ

lemma parametrix_coordinateSupport [T2Space X] [CompactSpace X]
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (A : FiniteCharts X)
    (hA : ∀ p : A.centers, tsupport (A.partition p) ⊆ (parametrixData J α hs ht p.val).source)
    (p : A.centers) : coordinateSupport A p ⊆
      Metric.closedBall (extChartAt Model p.val p.val) ((parametrixData J α hs ht p.val).radius/2) := by
  rintro q ⟨x,hx,rfl⟩
  exact (parametrixData J α hs ht p.val).source_image_subset ⟨x,hA p hx,rfl⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
