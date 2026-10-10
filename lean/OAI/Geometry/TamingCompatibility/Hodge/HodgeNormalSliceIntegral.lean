import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgePatchLocalInitial
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixFormWeak

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

lemma normal_slice_integral {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius)
    (F : Space → ℝ)
    (hF : Function.support F ⊆ normalMap E.metricExtension E.frameExtension q ''
      tsupport (E.normalCutoff : Space → ℝ)) :
    (∫ y, volumeDensity (E.metricExtension y) * F y) =
      ∫ z in E.weakSliceDomain q, normalDensity E.metricExtension E.frameExtension (q,z) *
        F (normalMap E.metricExtension E.frameExtension q z) := by
  let U := E.weakSliceDomain q
  let φ := normalMap E.metricExtension E.frameExtension q
  have hf : ∀ y, y ∉ φ '' U → volumeDensity (E.metricExtension y) * F y = 0 := by
    intro y hy
    have hFy : F y = 0 := by
      by_contra hn
      obtain ⟨z,hz,rfl⟩ := hF hn
      exact hy ⟨z,E.cutoff_weakSliceDomain hq hz,rfl⟩
    rw [hFy,mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf]
  have hi : InjOn φ U := (normalMap_slice_injective E.metricExtension E.frameExtension
    E.metric_smooth E.frame_smooth (extChartAt Model p p) E.centerFrame E.centerFrame_eq q).mono
      (fun _ hz => hz.1.1.1)
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (E.weakSliceDomain_open q).measurableSet
    (fun z (_ : z ∈ U) => ((normalMap_contDiff E.metricExtension E.frameExtension q).differentiable
      (by simp)).differentiableAt.hasFDerivAt.hasFDerivWithinAt) hi]
  apply setIntegral_congr_fun (E.weakSliceDomain_open q).measurableSet
  intro z _
  dsimp only
  rw [normalDensity,normal_density_jacobian E.metricExtension E.frameExtension E.metric_smooth
    E.frame_smooth E.metric_symmetric]
  change |(fderiv ℝ φ z).toLinearMap.det| *
      (volumeDensity (E.metricExtension (φ z)) * F (φ z)) =
    (|(fderiv ℝ φ z).toLinearMap.det| * volumeDensity (E.metricExtension (φ z))) * F (φ z)
  ring

end ParametrixData
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
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

def cutoffSection (q : Space) (t : ℝ) (u : W) : Space → W := fun z =>
  normalGauge J α ht p E.chart E.metricExtension E.frameExtension (q,z)
    (E.normalCutoff z • NormalHeatResidual.modelSection t u z)

lemma cutoffSection_tsupport (q : Space) (t : ℝ) (u : W) :
    tsupport (E.cutoffSection q t u) ⊆ tsupport (E.normalCutoff : Space → ℝ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  by_contra hn
  exact hz (by simp only [cutoffSection,image_eq_zero_of_notMem_tsupport hn,zero_smul,map_zero])

end ParametrixData
variable [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma leadingSlice_energy_point (hs : IsSmooth α) (p : A.centers) (q : Space)
    {t : ℝ} (htp : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a)
    {z : Space} (hz : z ∈ (E p).weakSliceDomain q) :
    let D := (E p).chart
    let g := (E p).metricExtension
    let B := (E p).frameExtension
    ⟪differential EuclideanEnergy.e (pulledA J α ht p.val D g B q) (pulledB J α ht p.val D g B q)
        (HodgeChart.rawVector J α ht p.val D a ∘ normalMap g B q) z,
      differential EuclideanEnergy.e (pulledA J α ht p.val D g B q) (pulledB J α ht p.val D g B q)
        ((E p).cutoffSection q t (coordinatePartition A p q • u)) z⟫ =
    ⟪HodgeChart.normalOperator J α ht p.val D (HodgeChart.rawVector J α ht p.val D a)
        (normalMap g B q z),
      HodgeChart.normalOperator J α ht p.val D (leadingSlice J α ht A E p q t u)
        (normalMap g B q z)⟫ := by
  dsimp only
  have he : (leadingSlice J α ht A E p q t u ∘
      normalMap (E p).metricExtension (E p).frameExtension q) =ᶠ[𝓝 z]
      (E p).cutoffSection q t (coordinatePartition A p q • u) :=
    leadingSlice_normal_nhds J α ht A E p q t u hz
  rw [← differential_congr_nhds EuclideanEnergy.e
    (pulledA J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension q)
    (pulledB J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension q) he]
  apply pulled_energy J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
    (E p).metric_smooth (E p).frame_smooth (E p).metric_symmetric q z
    ((E p).weakSliceDomain_normal hz).1.2
  · exact ((HodgeChart.rawVector_smooth J α ht p.val (E p).chart ha).contDiffAt
      ((E p).chart.domain_open.mem_nhds ((E p).actual_subset
        ((E p).weakSliceDomain_actual hz)))).differentiableAt (by simp)
  · exact (leadingSlice_smooth J α ht A E hE hs p q htp u).differentiable (by simp) |>.differentiableAt

include hE in
lemma leadingSlice_energy_integral (hs : IsSmooth α) (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    {t : ℝ} (htp : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a) :
    let D := (E p).chart
    let g := (E p).metricExtension
    let B := (E p).frameExtension
    (∫ y, chartDensity J α p.val y *
      ⟪HodgeChart.normalOperator J α ht p.val D (HodgeChart.rawVector J α ht p.val D a) y,
        HodgeChart.normalOperator J α ht p.val D (leadingSlice J α ht A E p q t u) y⟫) =
    ∫ z, normalDensity g B (q,z) *
      ⟪differential EuclideanEnergy.e (pulledA J α ht p.val D g B q) (pulledB J α ht p.val D g B q)
          (HodgeChart.rawVector J α ht p.val D a ∘ normalMap g B q) z,
        differential EuclideanEnergy.e (pulledA J α ht p.val D g B q) (pulledB J α ht p.val D g B q)
          ((E p).cutoffSection q t (coordinatePartition A p q • u)) z⟫ := by
  dsimp only
  let F := fun y =>
    ⟪HodgeChart.normalOperator J α ht p.val (E p).chart
        (HodgeChart.rawVector J α ht p.val (E p).chart a) y,
      HodgeChart.normalOperator J α ht p.val (E p).chart (leadingSlice J α ht A E p q t u) y⟫
  have hFs : Function.support F ⊆ tsupport (leadingSlice J α ht A E p q t u) := by
    intro y hy
    by_contra hn
    exact hy (by dsimp only [F]; rw [HodgeChart.normalOperator_zero_off J α ht p.val
      (E p).chart _ hn,inner_zero_right])
  have hd : (∫ y, chartDensity J α p.val y * F y) =
      ∫ y, volumeDensity ((E p).metricExtension y) * F y := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : F y = 0
    · simp only [hy,mul_zero]
    · obtain ⟨z,hz,rfl⟩ := leadingSlice_tsupport J α ht A E p q t u (hFs hy)
      rw [(E p).density_actual J α ht ((E p).weakSliceDomain_actual
        ((E p).cutoff_weakSliceDomain hq hz))]
  change (∫ y, chartDensity J α p.val y * F y) = _
  rw [hd,(E p).normal_slice_integral hq F (hFs.trans (leadingSlice_tsupport J α ht A E p q t u))]
  rw [setIntegral_congr_fun ((E p).weakSliceDomain_open q).measurableSet
    (fun z hz => congrArg (fun w => normalDensity (E p).metricExtension (E p).frameExtension (q,z) * w)
      (leadingSlice_energy_point J α ht A E hE hs p q htp u a ha hz).symm)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hn : z ∉ tsupport ((E p).cutoffSection q t (coordinatePartition A p q • u)) :=
    fun hh => hz ((E p).cutoff_weakSliceDomain hq ((E p).cutoffSection_tsupport q t _ hh))
  rw [differential_zero_off EuclideanEnergy.e _ _ _ hn,inner_zero_right,mul_zero]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
