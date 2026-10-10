import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgePatchPairing

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [T2Space X] [CompactSpace X] in
lemma partitionLeading_zero_center (p : A.centers) {q : Space}
    (hq : coordinatePartition A p q = 0) (t : ℝ) (y : Space) :
    partitionLeading J α ht A E p t (q,y) = 0 := by
  unfold partitionLeading leadingPatch KernelExtension.push
  split_ifs with hz
  · have hf := geometricNormalChart_symm_fst (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq hz
    simp only [leadingCoordinate,hf,hq,zero_mul]
    exact zero_smul ℝ (normalGauge J α ht p.val (E p).chart
      (E p).metricExtension (E p).frameExtension ((E p).normalChart.symm (q,y)))
  · rfl

omit [T2Space X] [CompactSpace X] in
lemma partitionResidual_zero_center (p : A.centers) {q : Space}
    (hq : coordinatePartition A p q = 0) (t : ℝ) (y : Space) :
    partitionResidual J α ht A E p t (q,y) = 0 := by
  unfold partitionResidual residualPatch KernelExtension.push
  split_ifs with hz
  · have hf := geometricNormalChart_symm_fst (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq hz
    simp only [residualCoordinate,hf,hq,zero_smul]
  · rfl

omit [T2Space X] [CompactSpace X] in
lemma leadingSliceForm_zero_center (p : A.centers) {q : Space}
    (hq : coordinatePartition A p q = 0) (t : ℝ) (u : W) :
    leadingSliceForm J α ht A E p q t u = 0 := by
  have hz : leadingSlice J α ht A E p q t u = 0 := by
    funext y
    simp only [leadingSlice,partitionLeading_zero_center J α ht A E p hq t y,zero_apply,Pi.zero_apply]
  funext x
  apply HodgeChart.manifoldTest_zero_off J α ht p.val (E p).chart
  rw [hz,tsupport_zero,Set.image_empty]
  exact Set.notMem_empty x

omit [T2Space X] [CompactSpace X] in
lemma residualSliceForm_zero_center (p : A.centers) {q : Space}
    (hq : coordinatePartition A p q = 0) (t : ℝ) (u : W) :
    residualSliceForm J α ht A E p q t u = 0 := by
  have hz : residualSlice J α ht A E p q t u = 0 := by
    funext y
    simp only [residualSlice,partitionResidual_zero_center J α ht A E p hq t y,zero_apply,Pi.zero_apply]
  funext x
  apply HodgeChart.manifoldTest_zero_off J α ht p.val (E p).chart
  rw [hz,tsupport_zero,Set.image_empty]
  exact Set.notMem_empty x

include hE in
lemma leadingSliceForm_smooth_all (hs : IsSmooth α) (p : A.centers) (q : Space)
    {t : ℝ} (htp : 0 < t) (u : W) : IsSmooth (leadingSliceForm J α ht A E p q t u) := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · exact leadingSliceForm_smooth J α ht A E hE hs p hq htp u
  · rw [leadingSliceForm_zero_center J α ht A E p
      (image_eq_zero_of_notMem_tsupport (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))) t u]
    exact TamingCompatibility.IsSmooth.zero

include hE in
lemma residualSliceForm_smooth_all (hs : IsSmooth α) (p : A.centers) (q : Space)
    {t : ℝ} (htp : 0 < t) (u : W) : IsSmooth (residualSliceForm J α ht A E p q t u) := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · exact residualSliceForm_smooth J α ht A E hE hs p hq htp u
  · rw [residualSliceForm_zero_center J α ht A E p
      (image_eq_zero_of_notMem_tsupport (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))) t u]
    exact TamingCompatibility.IsSmooth.zero

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldLocalization
open Set ManifoldForms
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X)

def squareMass (x : X) : ℝ := ∑ p : A.centers, (A.partition p x)^2

lemma squareMass_pos (x : X) : 0 < squareMass A x := by
  classical
  have he : ∃ p : A.centers, A.partition p x ≠ 0 := by
    by_contra h
    push Not at h
    have hh := partition_sum A x
    simp only [h,Finset.sum_const_zero] at hh
    norm_num at hh
  obtain ⟨p,hp⟩ := he
  exact (sq_pos_of_ne_zero hp).trans_le
    (Finset.single_le_sum (fun q _ => sq_nonneg (A.partition q x)) (Finset.mem_univ p))

lemma squareMass_smooth : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (squareMass A) := by
  exact ContMDiff.sum (fun p _ => (A.partition p).contMDiff.pow 2)

lemma squareMass_inv_smooth : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (fun x => (squareMass A x)⁻¹) :=
  (squareMass_smooth A).inv₀ (fun x => ne_of_gt (squareMass_pos A x))

lemma squareMass_normalized (x : X) :
    ∑ p : A.centers, ((squareMass A x)⁻¹*(A.partition p x)^2) = 1 := by
  rw [← Finset.mul_sum]
  exact inv_mul_cancel₀ (ne_of_gt (squareMass_pos A x))

end TamingCompatibility.ManifoldLocalization

namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open HodgeNormalSymbol (W)
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma pairing_basisForm (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (a : MetricForms.Form E 2) (j : Fin 6) :
    pairing g a (basisForm g b j) = coordinates b a j := by
  rw [← coordinates_pairing g hdim b hb]
  simp only [PiLp.inner_apply,coordinates_basisForm g b hb,RCLike.inner_apply,conj_trivial]
  simp

lemma basisForm_resolution (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (a : MetricForms.Form E 2) :
    ∑ j : Fin 6, pairing g a (basisForm g b j) • basisForm g b j = a := by
  simp_rw [pairing_basisForm g hdim b hb]
  exact (reconstruct_apply g b (coordinates b a)).symm.trans (reconstruct_coordinates g hdim b hb a)

end TamingCompatibility.HodgeFrame

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

def globalFrame (p : A.centers) (j : Fin 6) : TwoForm X :=
  HodgeChart.manifoldTest J α ht p.val (D p).chart
    (fun z => coordinatePartition A p z • EuclideanSpace.basisFun (Fin 6) ℝ j)

include hD in
lemma globalFrame_smooth (hs : IsSmooth α) (p : A.centers) (j : Fin 6) :
    IsSmooth (globalFrame J α ht A D p j) := by
  have hp := coordinatePartition_smooth_compact A p
  have hc : HasCompactSupport (fun z => coordinatePartition A p z • EuclideanSpace.basisFun (Fin 6) ℝ j) :=
    hp.2.smul_right
  have hsup : tsupport (fun z => coordinatePartition A p z • EuclideanSpace.basisFun (Fin 6) ℝ j) ⊆
      coordinateSupport A p :=
    (tsupport_smul_subset_left _ _).trans (coordinatePartition_tsupport A p)
  apply HodgeChart.manifoldTest_smooth J α hs ht p.val (D p).chart
    (hp.1.smul contDiff_const) hc
  apply hsup.trans
  rintro q ⟨x,hx,rfl⟩
  have hh := (D p).source_image_subset ⟨x,hD p hx,rfl⟩
  exact (D p).actual_subset ((D p).centers_actual
    (Metric.closedBall_subset_closedBall (by linarith [(D p).radius_pos]) hh))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
