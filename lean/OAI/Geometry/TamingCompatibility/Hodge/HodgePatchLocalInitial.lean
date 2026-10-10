import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAtlasPatches

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open Filter Set MeasureTheory HodgeNormalSymbol FirstJetGauge OrthogonalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalGauge normalFirst
lemma leadingCoordinate_initial_local (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {q : Space} (hactual : ActualData J α ht p D q g B)
    (ψ χ : Space → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1)
    (f : Space → W) (hf : ∀ z ∈ tsupport χ, ContinuousAt f (normalMap g B q z)) :
    Tendsto (fun t : ℝ => ∫ z : Space,
      (ψ q * χ z * FlatHeat.heat t z * normalDensity g B (q,z)) •
        (normalGauge J α ht p D g B (q,z)).adjoint (f (normalMap g B q z)))
      (𝓝[>] 0) (𝓝 (ψ q • f q)) := by
  let F : Space → W := fun z => (ψ q * χ z * normalDensity g B (q,z)) •
    (normalGauge J α ht p D g B (q,z)).adjoint (f (normalMap g B q z))
  have hU : Continuous (fun z : Space => normalGauge J α ht p D g B (q,z)) :=
    continuous_iff_continuousAt.mpr (fun z =>
      ((normalGauge_smooth J α ht p D g B hs hg hB (hactual.center J α ht p D g B).1).comp z
        (contDiffAt_const.prodMk contDiffAt_id)).continuousAt)
  have hUa : Continuous (fun z : Space => (normalGauge J α ht p D g B (q,z)).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp hU
  have hmap : Continuous (normalMap g B q) := (normalMap_contDiff g B q).continuous
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun z => by
    by_cases hz : z ∈ tsupport χ
    · exact (((continuous_const.mul hχ).mul
        ((normalDensity_continuous g B hg hB).comp
          (continuous_const.prodMk continuous_id))).continuousAt).smul
        (hUa.continuousAt.clm_apply ((hf z hz).comp hmap.continuousAt))
    · apply (continuousAt_const : ContinuousAt (fun _ : Space => (0 : W)) z).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with y hy
      simp only [mem_compl_iff] at hy
      simp [F,image_eq_zero_of_notMem_tsupport hy])
  have hFc : HasCompactSupport F := by
    apply hχc.mono
    intro z hz
    change χ z ≠ 0
    intro he
    exact hz (by simp [F,he])
  have hF0 : F 0 = ψ q • f q := by
    simp only [F,hχ0,normalDensity_zero J α ht p D g B hactual,normalGauge_zero,mul_one,
      ContinuousLinearMap.adjoint_one,one_apply_eq_self,normalMap_zero]
  have hh := FlatHeat.heat_approximate_identity F (hF.integrable_of_hasCompactSupport hFc) hF.continuousAt
  rw [hF0] at hh
  convert hh using 1
  funext t
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [F,smul_smul]
  congr 1
  ring

variable [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
include hE in
omit [T2Space X] in
lemma partitionLeading_initial_local (hs : IsSmooth α) (p : A.centers) (q : Space)
    (f : Space → W) (hf : ContinuousOn f (E p).chart.domain) :
    Tendsto (fun t : ℝ => ∫ y : Space, chartDensity J α p.val y •
      (partitionLeading J α ht A E p t (q,y)).adjoint (f y))
      (𝓝[>] 0) (𝓝 (coordinatePartition A p q • f q)) := by
  simp_rw [partitionLeading_density J α ht A E hE]
  have hsub : Function.support (coordinatePartition A p) ×ˢ
      Function.support ((E p).normalCutoff : Space → ℝ) ⊆ (E p).normalChart.source :=
    ((Set.prod_mono Set.Subset.rfl (subset_tsupport _)).trans
      (partition_patch_support J α ht A E hE p)).trans (E p).normalCompact_source
  simp_rw [partitionLeading,leadingPatch_change J α ht p.val (E p).chart
    (E p).metricExtension (E p).frameExtension (E p).metric_smooth (E p).frame_smooth
    (extChartAt Model p.val p.val) (E p).centerFrame (E p).centerFrame_eq
    (E p).metric_symmetric (coordinatePartition A p) (E p).normalCutoff hsub]
  by_cases hq : coordinatePartition A p q = 0
  · simp [hq]
  · apply leadingCoordinate_initial_local J α ht p.val (E p).chart (E p).metricExtension
      (E p).frameExtension hs (E p).metric_smooth (E p).frame_smooth ((E p).actual
        (coordinatePartition_centerSupport J α ht A E hE p (subset_tsupport _ hq)))
      (coordinatePartition A p) (E p).normalCutoff (E p).normalCutoff.continuous
      (E p).normalCutoff.hasCompactSupport
      ((E p).normalCutoff.one_of_mem_closedBall (Metric.mem_closedBall_self (E p).normalCutoff.rIn_pos.le)) f
    intro z hz
    have hzK : (q,z) ∈ (E p).normalCompact :=
      partition_patch_support J α ht A E hE p ⟨hq,hz⟩
    have hy := (E p).actual_subset ((E p).tube hzK).2
    exact (hf _ hy).continuousAt ((E p).chart.domain_open.mem_nhds hy)

include hE in
omit [T2Space X] in
lemma partitionLeading_initial_form (hs : IsSmooth α) (p : A.centers) (q : Space)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ y : Space, chartDensity J α p.val y •
      (partitionLeading J α ht A E p t (q,y)).adjoint
        (HodgeChart.rawVector J α ht p.val (E p).chart a y))
      (𝓝[>] 0) (𝓝 (coordinatePartition A p q •
        HodgeChart.rawVector J α ht p.val (E p).chart a q)) :=
  partitionLeading_initial_local J α ht A E hE hs p q _
    (HodgeChart.rawVector_smooth J α ht p.val (E p).chart ha).continuousOn

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.CoordinateOperator
open EuclideanEnergy HodgeNormalSymbol OperatorCalculus
open scoped RealInnerProductSpace

lemma sum_pullCoefficient_inverse (a : Fin 4 → W →L[ℝ] Q)
    (L : V ≃L[ℝ] V) (du : V →L[ℝ] W) :
    (∑ j, pullCoefficient a L.symm.toContinuousLinearMap j (du (L (e j)))) =
      ∑ i, a i (du (e i)) := by
  simp only [pullCoefficient,_root_.sum_apply,_root_.smul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, (L.symm (e i) j) • a i (du (L (e j)))) =
        a i (du (L (∑ j, (L.symm (e i) j) • e j))) := by
      simp only [map_sum,map_smul]
    _ = a i (du (e i)) := by rw [← basis_expansion (L.symm (e i)),L.apply_symm_apply]

lemma firstOrder_inverse_pull (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (u : V → W) (φ : V → V) (z : V) (L : V ≃L[ℝ] V)
    (hφ : HasFDerivAt φ L.toContinuousLinearMap z) (hu : DifferentiableAt ℝ u (φ z)) :
    firstOrder (fun i y => pullCoefficient (fun k => a k (φ y)) L.symm.toContinuousLinearMap i)
      (fun y => b (φ y)) (u ∘ φ) z = firstOrder a b u (φ z) := by
  simp only [firstOrder,(hu.hasFDerivAt.comp z hφ).fderiv,ContinuousLinearMap.comp_apply,
    Function.comp_apply]
  exact congrArg (fun w => w + b (φ z) (u (φ z)))
    (sum_pullCoefficient_inverse (fun k => a k (φ z)) L (fderiv ℝ u (φ z)))

end TamingCompatibility.GeometricHilbert.CoordinateOperator

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms HodgeNormalSymbol EuclideanEnergy OperatorCalculus CoordinateOperator NormalJets
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma pulled_firstOrder (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (q z : Space)
    (hL : (normalDifferential g B q z).IsInvertible)
    (u : Space → W) (hu : DifferentiableAt ℝ u (normalMap g B q z)) :
    differential e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q)
      (u ∘ normalMap g B q) z = HodgeChart.normalOperator J α ht p D u (normalMap g B q z) := by
  obtain ⟨L,hL⟩ := hL
  have hφ : HasFDerivAt (normalMap g B q) L.toContinuousLinearMap z := by
    rw [hL]
    exact centeredDisplacement_hasFDerivAt g B hg hB hsym q z
  unfold differential pulledA pulledB
  rw [← hL,ContinuousLinearMap.inverse_equiv]
  exact firstOrder_inverse_pull (HodgeChart.normalA J α ht p D) (HodgeChart.normalB J α ht p D)
    u (normalMap g B q) z L hφ hu

lemma pulled_energy (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (q z : Space)
    (hL : (normalDifferential g B q z).IsInvertible)
    (u v : Space → W) (hu : DifferentiableAt ℝ u (normalMap g B q z))
    (hv : DifferentiableAt ℝ v (normalMap g B q z)) :
    ⟪differential e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q)
      (u ∘ normalMap g B q) z,
      differential e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q)
      (v ∘ normalMap g B q) z⟫ =
    ⟪HodgeChart.normalOperator J α ht p D u (normalMap g B q z),
      HodgeChart.normalOperator J α ht p D v (normalMap g B q z)⟫ := by
  rw [pulled_firstOrder J α ht p D g B hg hB hsym q z hL u hu,
    pulled_firstOrder J α ht p D g B hg hB hsym q z hL v hv]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
