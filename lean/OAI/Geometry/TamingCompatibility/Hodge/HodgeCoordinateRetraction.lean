import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeFiniteFrameResolution

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

def coordinateEncode (p : A.centers) (q : Space) : W →L[ℝ] FrameSpace A :=
  ContinuousLinearMap.pi (fun i => innerSL ℝ
    (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q))

def coordinateDecode (p : A.centers) (q : Space) : FrameSpace A →L[ℝ] W :=
  (squareMass A ((extChartAt Model p.val).symm q))⁻¹ • ∑ i : A.centers × Fin 6,
    (ContinuousLinearMap.proj i : FrameSpace A →L[ℝ] ℝ).smulRight
      (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q)

include hD in
lemma coordinateEncode_smooth (hs : IsSmooth α) (p : A.centers) :
    ContDiffOn ℝ ∞ (coordinateEncode J α ht A D p) (D p).chart.domain := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_pi.mpr
  intro i
  exact (HodgeChart.rawVector_smooth J α ht p.val (D p).chart
    (globalFrame_smooth J α ht A D hD hs i.1 i.2)).inner ℝ contDiffOn_const

include hD in
lemma coordinateDecode_smooth (hs : IsSmooth α) (p : A.centers) :
    ContDiffOn ℝ ∞ (coordinateDecode J α ht A D p) (D p).chart.domain := by
  have hmass := (((squareMass_inv_smooth A).comp_contMDiffOn
      (contMDiffOn_extChartAt_symm p.val)).contDiffOn).mono (D p).chart.domain_subset
  have hsum : ContDiffOn ℝ ∞ (fun q => ∑ i : A.centers × Fin 6,
      (ContinuousLinearMap.proj i : FrameSpace A →L[ℝ] ℝ).smulRight
        (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q))
      (D p).chart.domain := by
    apply ContDiffOn.sum
    intro i _
    exact contDiffOn_const.smulRight (HodgeChart.rawVector_smooth J α ht p.val (D p).chart
      (globalFrame_smooth J α ht A D hD hs i.1 i.2))
  exact hmass.smul hsum

omit [T2Space X] [CompactSpace X] in
lemma coordinateEncode_rawVector (p : A.centers) (a : TwoForm X) {q : Space}
    (hq : q ∈ (D p).chart.domain) :
    coordinateEncode J α ht A D p q (HodgeChart.rawVector J α ht p.val (D p).chart a q) =
      frameEncode J α ht A D ((extChartAt Model p.val).symm q) (a ((extChartAt Model p.val).symm q)) := by
  ext i
  change ⟪HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q,
    HodgeChart.rawVector J α ht p.val (D p).chart a q⟫ = _
  rw [real_inner_comm]
  unfold HodgeChart.rawVector
  rw [coordinates_pairing _ (by simp [Space]) _ ((D p).chart.frame_gram q hq),
    GeometricAdjoint.pairing_two_chart J α ht p.val a (globalFrame J α ht A D i.1 i.2)
      ((D p).chart.domain_subset hq)]
  rfl

omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_apply (p : A.centers) (q : Space) (v : FrameSpace A) :
    coordinateDecode J α ht A D p q v = (squareMass A ((extChartAt Model p.val).symm q))⁻¹ •
      ∑ i : A.centers × Fin 6, v i •
        HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q := by
  change (squareMass A ((extChartAt Model p.val).symm q))⁻¹ • ((∑ i : A.centers × Fin 6,
    (ContinuousLinearMap.proj i : FrameSpace A →L[ℝ] ℝ).smulRight
      (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q)) v) = _
  simp only [_root_.sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]

omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_rawVector (p : A.centers) (q : Space) (v : FrameSpace A) :
    coordinateDecode J α ht A D p q v = HodgeChart.rawVector J α ht p.val (D p).chart
      (fun x => frameDecode J α ht A D x v) q := by
  rw [coordinateDecode_apply,Fintype.sum_prod_type]
  let L : MetricForms.Form Space 2 →L[ℝ] W :=
    HodgeFrame.coordinates (fun i => (D p).chart.frame i q) ∘L
      ContinuousAlternatingMap.compContinuousLinearMapCLM
        (mfderiv Model Model (extChartAt Model p.val).symm q)
  change (squareMass A ((extChartAt Model p.val).symm q))⁻¹ •
    (∑ i : A.centers, ∑ j : Fin 6, v (i,j) • L (globalFrame J α ht A D i j ((extChartAt Model p.val).symm q))) = _
  simp only [HodgeChart.rawVector,ManifoldForms.pullback,frameDecode_apply]
  change _ = L _
  simp only [Finset.smul_sum,smul_smul]
  have he (g : A.centers → Fin 6 → MetricForms.Form Space 2) (c : A.centers → Fin 6 → ℝ) :
      L (∑ i : A.centers, ∑ j : Fin 6, c i j • g i j) = ∑ i : A.centers, ∑ j : Fin 6, c i j • L (g i j) := by
    simp only [map_sum,map_smul]
  exact (he (fun i j => globalFrame J α ht A D i j ((extChartAt Model p.val).symm q))
    (fun i j => (squareMass A ((extChartAt Model p.val).symm q))⁻¹*v (i,j))).symm

include hD in
omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_encode_raw (p : A.centers) (a : TwoForm X) {q : Space}
    (hq : q ∈ (D p).chart.domain) :
    coordinateDecode J α ht A D p q
      (coordinateEncode J α ht A D p q (HodgeChart.rawVector J α ht p.val (D p).chart a q)) =
      HodgeChart.rawVector J α ht p.val (D p).chart a q := by
  rw [coordinateEncode_rawVector J α ht A D p a hq,coordinateDecode_rawVector]
  change HodgeFrame.coordinates _ ((frameDecode J α ht A D ((extChartAt Model p.val).symm q)
    (frameEncode J α ht A D ((extChartAt Model p.val).symm q) (a ((extChartAt Model p.val).symm q)))).compContinuousLinearMap _) = _
  erw [frameDecode_encode J α ht A D hD]
  rfl

include hD in
omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_encode (p : A.centers) {q : Space} (hq : q ∈ (D p).chart.domain) (v : W) :
    coordinateDecode J α ht A D p q (coordinateEncode J α ht A D p q v) = v := by
  let a := HodgeChart.manifoldTest J α ht p.val (D p).chart (fun _ => v)
  have ha : HodgeChart.rawVector J α ht p.val (D p).chart a q = v := by
    unfold HodgeChart.rawVector a
    rw [HodgeChart.pullback_manifoldTest J α ht p.val (D p).chart _ ((D p).chart.domain_subset hq)]
    exact coordinates_reconstruct _ _ ((D p).chart.frame_gram q hq) v
  rw [← ha]
  exact coordinateDecode_encode_raw J α ht A D hD p a hq

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
