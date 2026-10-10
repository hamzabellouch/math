import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgePatchAllCenters

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms HodgeNormalSymbol
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma reconstruct_basisFun (g : Metric E) (b : Fin 4 → E) (j : Fin 6) :
    reconstruct g b (EuclideanSpace.basisFun (Fin 6) ℝ j) = basisForm g b j := by
  rw [reconstruct_apply]
  simp
end TamingCompatibility.HodgeFrame

namespace TamingCompatibility.GeometricAdjoint
open ManifoldForms ManifoldHodge
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
lemma pairing_two_chart (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (a b : TwoForm X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    MetricForms.pairing (coordinateMetric J α ht p z)
      (ManifoldForms.pullback a (extChartAt Model p).symm z)
      (ManifoldForms.pullback b (extChartAt Model p).symm z) =
      pairing J α ht a b ((extChartAt Model p).symm z) := by
  have he := MetricForms.pairing_two_comp (E := Space) (D := Space) (coordinateMetric J α ht p z)
    (pointMetric J α ht ((extChartAt Model p).symm z)) (inverseChartEquiv p z hz)
    (coordinateMetric_pullback J α ht p hz) (by simp [Space])
    (a ((extChartAt Model p).symm z)) (b ((extChartAt Model p).symm z))
  erw [inverseChartEquiv_coe] at he
  exact he
end TamingCompatibility.GeometricAdjoint

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma globalFrame_zero (p : A.centers) (j : Fin 6) {x : X} (hx : A.partition p x = 0) :
    globalFrame J α ht A D p j x = 0 := by
  classical
  unfold globalFrame HodgeChart.manifoldTest chartLift
  split_ifs with hxs
  · rw [HodgeChart.coordinateTest,coordinatePartition_apply A p hxs,hx,zero_smul,map_zero]
    rfl
  · rfl

omit [T2Space X] [CompactSpace X] in
lemma globalFrame_pullback (p : A.centers) (j : Fin 6) {z : Space}
    (hz : z ∈ (extChartAt Model p.val).target) :
    ManifoldForms.pullback (globalFrame J α ht A D p j) (extChartAt Model p.val).symm z =
      coordinatePartition A p z • basisForm (coordinateMetric J α ht p.val z)
        (fun i => (D p).chart.frame i z) j := by
  rw [globalFrame,HodgeChart.pullback_manifoldTest J α ht p.val (D p).chart _ hz]
  rw [HodgeChart.coordinateTest,map_smul,reconstruct_basisFun]

omit [T2Space X] [CompactSpace X] in
lemma globalFrame_resolution_chart (p : A.centers) (a : TwoForm X) {z : Space}
    (hz : z ∈ (extChartAt Model p.val).target) (hzD : z ∈ (D p).chart.domain) :
    ∑ j : Fin 6,
      GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D p j) ((extChartAt Model p.val).symm z) •
      globalFrame J α ht A D p j ((extChartAt Model p.val).symm z) =
        (A.partition p ((extChartAt Model p.val).symm z))^2 • a ((extChartAt Model p.val).symm z) := by
  classical
  let L := (inverseChartEquiv p.val z hz).symm.continuousAlternatingMapCongrLeft
    (ι := Fin 2) (F := ℝ)
  have hL (c : TwoForm X) : L (c ((extChartAt Model p.val).symm z)) =
      ManifoldForms.pullback c (extChartAt Model p.val).symm z := by
    change (c _).compContinuousLinearMap (inverseChartEquiv p.val z hz).toContinuousLinearMap = _
    rw [inverseChartEquiv_coe]
    rfl
  apply L.injective
  simp only [map_sum,map_smul]
  have hg (j : Fin 6) : L (globalFrame J α ht A D p j ((extChartAt Model p.val).symm z)) =
      coordinatePartition A p z • basisForm (coordinateMetric J α ht p.val z)
        (fun i => (D p).chart.frame i z) j := by
    rw [hL,globalFrame_pullback J α ht A D p j hz]
  have hpair (j : Fin 6) :
      GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D p j) ((extChartAt Model p.val).symm z) =
      coordinatePartition A p z * MetricForms.pairing (coordinateMetric J α ht p.val z)
        (L (a ((extChartAt Model p.val).symm z)))
        (basisForm (coordinateMetric J α ht p.val z) (fun i => (D p).chart.frame i z) j) := by
    rw [← GeometricAdjoint.pairing_two_chart J α ht p.val a (globalFrame J α ht A D p j) hz,
      globalFrame_pullback J α ht A D p j hz,MetricForms.pairing_smul_right,hL]
  simp_rw [hg,hpair,smul_smul]
  have hscalar (b : ℝ) : coordinatePartition A p z*b*coordinatePartition A p z =
      (coordinatePartition A p z)^2*b := by ring
  simp_rw [hscalar,← smul_smul]
  rw [← Finset.smul_sum,basisForm_resolution _ (by simp [Space]) _ ((D p).chart.frame_gram z hzD)]
  rw [coordinatePartition,Set.indicator_of_mem hz]

include hD in
omit [T2Space X] [CompactSpace X] in
lemma globalFrame_resolution (p : A.centers) (a : TwoForm X) (x : X) :
    ∑ j : Fin 6, GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D p j) x •
      globalFrame J α ht A D p j x = (A.partition p x)^2 • a x := by
  classical
  by_cases hp : A.partition p x = 0
  · simp only [globalFrame_zero J α ht A D p _ hp,smul_zero,Finset.sum_const_zero,hp,
      zero_pow (by norm_num : 2 ≠ 0),zero_smul]
  have hx : x ∈ (extChartAt Model p.val).source := A.subordinate p (subset_tsupport _ hp)
  have hz := (extChartAt Model p.val).map_source hx
  have hzD : extChartAt Model p.val x ∈ (D p).chart.domain := by
    have hh := (D p).source_image_subset ⟨x,hD p (subset_tsupport _ hp),rfl⟩
    exact (D p).actual_subset ((D p).centers_actual
      (Metric.closedBall_subset_closedBall (by linarith [(D p).radius_pos]) hh))
  have he := globalFrame_resolution_chart J α ht A D p a hz hzD
  let P : X → Prop := fun y =>
    ∑ j : Fin 6, GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D p j) y •
      globalFrame J α ht A D p j y = (A.partition p y)^2 • a y
  exact (congrArg P ((extChartAt Model p.val).left_inv hx)).mp he

include hD in
omit [T2Space X] [CompactSpace X] in
lemma globalFrame_full_resolution (a : TwoForm X) (x : X) :
    ∑ p : A.centers, ∑ j : Fin 6,
      ((squareMass A x)⁻¹ * GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D p j) x) •
        globalFrame J α ht A D p j x = a x := by
  simp_rw [← smul_smul,← Finset.smul_sum,globalFrame_resolution J α ht A D hD]
  rw [← Finset.sum_smul]
  change (squareMass A x)⁻¹ • squareMass A x • a x = a x
  rw [smul_smul,inv_mul_cancel₀ (ne_of_gt (squareMass_pos A x)),one_smul]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
lemma Smooth.sum {ι : Type*} (s : Finset ι) {k : ℕ} (a : ι → Form X k)
    (ha : ∀ i ∈ s, Smooth (a i)) : Smooth (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Smooth.zero (X := X) (k := k))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (ha i (Finset.mem_insert_self i s)).add (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))
end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

abbrev FrameSpace := (A.centers × Fin 6) → ℝ

def frameEncode (x : X) : MetricForms.Form Space 2 →L[ℝ] FrameSpace A :=
  ContinuousLinearMap.pi (fun i => (MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2).flip
    (globalFrame J α ht A D i.1 i.2 x))

def frameDecode (x : X) : FrameSpace A →L[ℝ] MetricForms.Form Space 2 :=
  (squareMass A x)⁻¹ • ∑ p : A.centers, ∑ j : Fin 6,
    (ContinuousLinearMap.proj (p,j) : FrameSpace A →L[ℝ] ℝ).smulRight (globalFrame J α ht A D p j x)

omit [T2Space X] [CompactSpace X] in
lemma frameEncode_apply (a : TwoForm X) (x : X) (i : A.centers × Fin 6) :
    frameEncode J α ht A D x (a x) i =
      GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D i.1 i.2) x := rfl

omit [T2Space X] [CompactSpace X] in
lemma frameDecode_apply (x : X) (v : FrameSpace A) :
    frameDecode J α ht A D x v = ∑ p : A.centers, ∑ j : Fin 6,
      ((squareMass A x)⁻¹ * v (p,j)) • globalFrame J α ht A D p j x := by
  change (squareMass A x)⁻¹ • ((∑ p : A.centers, ∑ j : Fin 6,
    (ContinuousLinearMap.proj (p,j) : FrameSpace A →L[ℝ] ℝ).smulRight
      (globalFrame J α ht A D p j x)) v) = _
  rw [_root_.sum_apply]
  simp only [_root_.sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,
    Finset.smul_sum,smul_smul]

include hD in
omit [T2Space X] [CompactSpace X] in
lemma frameDecode_encode (x : X) (v : MetricForms.Form Space 2) :
    frameDecode J α ht A D x (frameEncode J α ht A D x v) = v := by
  rw [frameDecode_apply]
  exact globalFrame_full_resolution J α ht A D hD (fun _ => v) x

def frameProjection (x : X) : FrameSpace A →L[ℝ] FrameSpace A :=
  frameEncode J α ht A D x ∘L frameDecode J α ht A D x

include hD in
omit [T2Space X] [CompactSpace X] in
lemma frameProjection_idempotent (x : X) :
    frameProjection J α ht A D x * frameProjection J α ht A D x = frameProjection J α ht A D x := by
  ext v i
  change frameEncode J α ht A D x
    (frameDecode J α ht A D x (frameEncode J α ht A D x (frameDecode J α ht A D x v))) i = _
  rw [frameDecode_encode J α ht A D hD]
  rfl

include hD in
omit [T2Space X] [CompactSpace X] in
lemma frameProjection_encode (x : X) (v : MetricForms.Form Space 2) :
    frameProjection J α ht A D x (frameEncode J α ht A D x v) = frameEncode J α ht A D x v := by
  change frameEncode J α ht A D x (frameDecode J α ht A D x (frameEncode J α ht A D x v)) = _
  rw [frameDecode_encode J α ht A D hD]

include hD in
lemma frameEncode_section_smooth (hs : IsSmooth α) (a : TwoForm X) (ha : IsSmooth a) :
    ContMDiff Model 𝓘(ℝ,FrameSpace A) ∞ (fun x => frameEncode J α ht A D x (a x)) := by
  apply contMDiff_pi_space.mpr
  intro i
  exact GeometricAdjoint.pairing_two_smooth J α hs ht ha (globalFrame_smooth J α ht A D hD hs i.1 i.2)

include hD in
lemma frameDecode_section_smooth (hs : IsSmooth α) (v : X → FrameSpace A)
    (hv : ContMDiff Model 𝓘(ℝ,FrameSpace A) ∞ v) :
    IsSmooth (fun x => frameDecode J α ht A D x (v x)) := by
  have h (p : A.centers) (j : Fin 6) :
      Smooth (fun x => ((squareMass A x)⁻¹ * v x (p,j)) • globalFrame J α ht A D p j x) :=
    Smooth.fun_smul ((squareMass_inv_smooth A).mul (contMDiff_pi_space.mp hv (p,j)))
      (globalFrame_smooth J α ht A D hD hs p j)
  have hh := Smooth.sum Finset.univ (fun p : A.centers => ∑ j : Fin 6,
    (fun x => ((squareMass A x)⁻¹ * v x (p,j)) • globalFrame J α ht A D p j x))
    (fun p _ => Smooth.sum Finset.univ _ (fun j _ => h p j))
  have he : (fun x => frameDecode J α ht A D x (v x)) =
      ∑ p : A.centers, ∑ j : Fin 6,
        (fun x => ((squareMass A x)⁻¹ * v x (p,j)) • globalFrame J α ht A D p j x) := by
    funext x
    simp only [Finset.sum_apply,frameDecode_apply]
    rfl
  rw [he]
  exact hh

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
