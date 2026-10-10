import Mathlib
import OAI.Geometry.CubicTorus.Profiles.AxisCircleLebesgue

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisFixedHeights_null : volume axisFixedHeights=0 := by
  change volume ({0}∪{((1/2 : ℝ) : AxisCircle)})=0
  exact measure_union_null (axisCircle_singleton_null _) (axisCircle_singleton_null _)

lemma normal_zero_on_cell_seam {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {b : Fin 3 → Bool}
    (hsg : ∀ i : Fin 3,∀ x : Cover,x i∈Ioo (1/2 : ℝ) 1 →
      quotientMap x∈frontier (openRepresentative E) →
      if b i then 0<N x i else N x i<0)
    {x : Cover} (hx : quotientMap x∈frontier (openRepresentative E))
    (i : Fin 3) (hi : x i∈Icc (0 : ℝ) 1) (hn : N x i=0) :
    (x i : AxisCircle)∈axisFixedHeights := by
  by_cases h0 : x i=0
  · simp [axisFixedHeights,h0]
  by_cases h1 : x i=1
  · simp [axisFixedHeights,h1,AddCircle.coe_period]
  by_cases hhalf : x i=1/2
  · simp [axisFixedHeights,hhalf]
  exfalso
  have hpos : 0<x i := lt_of_le_of_ne hi.1 (Ne.symm h0)
  have hlt : x i<1 := lt_of_le_of_ne hi.2 h1
  have hbad : ∀ (y : Cover),y i∈Ioo (1/2 : ℝ) 1 →
      quotientMap y∈frontier (openRepresentative E) → N y i=0 → False := by
    intro y hy hyb hy0
    have hh := hsg i y hy hyb
    rw [hy0] at hh
    cases b i <;> simp at hh
  rcases lt_or_gt_of_ne hhalf with hlo|hhi
  · let y := (axisReflection i).cover x+latticeVector (Pi.single i (1 : ℤ))
    have hyi : y i=1-x i := by
      simp only [y,PiLp.add_apply,axisReflection_cover_apply,ite_true,latticeVector,
        Pi.single_eq_same,Int.cast_one]
      ring
    have hyb : quotientMap y∈frontier (openRepresentative E) := by
      rw [show y=(axisReflection i).cover x+latticeVector (Pi.single i (1 : ℤ)) from rfl,
        quotientMap_add,quotientMap_latticeVector,add_zero,(axisReflection i).commute]
      exact (reflection_invariant_frontier hmin.1.1 hR i _).mpr hx
    have hny : N y i=0 := by
      rw [show y=(axisReflection i).cover x+latticeVector (Pi.single i (1 : ℤ)) from rfl,
        hp,(axisReflection i).normal_equivariant hV hE hmin (hR i) hμ hN hp hae x hx]
      simp only [axisReflection_cover_apply,ite_true,hn,neg_zero]
    exact hbad y (by rw [hyi]; constructor <;> linarith) hyb hny
  · exact hbad x ⟨hhi,hlt⟩ hx hn

theorem strict_normal_component_ne_zero_ae {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {b : Fin 3 → Bool}
    (hsg : ∀ i : Fin 3,∀ x : Cover,x i∈Ioo (1/2 : ℝ) 1 →
      quotientMap x∈frontier (openRepresentative E) →
      if b i then 0<N x i else N x i<0) (i : Fin 3) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),((z.2 : Cover) i)≠0 := by
  have hμO := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμO
  have hnull := axial_null_normal_sq hH i axisFixedHeights_finite.measurableSet axisFixedHeights_null
  filter_upwards [hae,hbd,hnull] with z he hz hzs
  intro hzero
  have hzi : (z.1 : Cover) i∈Icc (0 : ℝ) 1 := by
    obtain ⟨y,hy,hye⟩ := z.1.property
    rw [←hye]
    exact ⟨hy.1 i,hy.2 i⟩
  have hseam := normal_zero_on_cell_seam hV hE hmin hR hμ hN hp hae hsg hz i hzi
    (by rw [he,hzero])
  have hh := hzs hseam
  rw [hzero] at hh
  norm_num at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialAreaMarginal (μ : FiniteMeasure NormalBundle) (i : Fin 3) : FiniteMeasure AxisCircle :=
  μ.map (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle))

lemma normal_transverse_positive_ae {μ : FiniteMeasure NormalBundle}
    (hn : ∀ i : Fin 3,∀ᵐ z ∂(μ : Measure NormalBundle),((z.2 : Cover) i)≠0) (i : Fin 3) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),0<1-((z.2 : Cover) i)^2 := by
  let j := i.succAbove (0 : Fin 2)
  have hji : j≠i := Fin.succAbove_ne i 0
  filter_upwards [hn j] with z hz
  have hh := normalSphere_two_sq_le z.2 hji
  have hj := sq_pos_of_ne_zero hz
  linarith

theorem axialAreaMarginal_absolutelyContinuous {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (hn : ∀ i : Fin 3,∀ᵐ z ∂(μ : Measure NormalBundle),((z.2 : Cover) i)≠0) (i : Fin 3) :
    (axialAreaMarginal μ i : Measure AxisCircle)≪volume := by
  have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1-((z.2 : Cover) i)^2)) :=
    (continuous_const.sub ((normal_component_continuous i).pow 2)).measurable.ennreal_ofReal
  have hpos : ∀ᵐ z ∂(μ : Measure NormalBundle),ENNReal.ofReal (1-((z.2 : Cover) i)^2)≠0 := by
    filter_upwards [normal_transverse_positive_ae hn i] with z hz
    exact (ENNReal.ofReal_pos.mpr hz).ne'
  have hac := withDensity_absolutelyContinuous' hw.aemeasurable hpos
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hh := axialSurfaceMarginal_absolutelyContinuous hH i hz
  change Measure.map _ _ s=0 at hh
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh
  change Measure.map _ _ s=0
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs]
  exact hac hh

lemma isMinimizerAt_nonstandard_strict_signs_of_actual_normal {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ b : Fin 3 → Bool,∀ i : Fin 3,∀ x : Cover,x i∈Ioo (1/2 : ℝ) 1 →
      quotientMap x∈frontier (openRepresentative E) →
      if b i then 0<N x i else N x i<0 := by
  obtain ⟨μ',H',N',b,hμ',hN',hp',hae',hb',hsg,_⟩ :=
    isMinimizerAt_nonstandard_strict_octant hV hmin hc hstd hR
  refine ⟨b,?_⟩
  intro i x hxi hx
  obtain ⟨w,hw⟩ := isMinimizerAt_normal_unique ⟨hV.1,by linarith [hV.2]⟩ hE hmin x hx
  have he := (hw μ hμ N hN hp hae).trans (hw μ' hμ' N' hN' hp' hae').symm
  rw [he]
  exact hsg i x hxi hx

theorem isMinimizerAt_nonstandard_area_marginals {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ μ : FiniteMeasure NormalBundle,IsNormalMeasure E μ ∧
      (∀ i : Fin 3,∀ᵐ z ∂(μ : Measure NormalBundle),((z.2 : Cover) i)≠0) ∧
      ∀ i : Fin 3,(axialAreaMarginal μ i : Measure AxisCircle)≪volume := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  obtain ⟨μ,H,hμ,hCMC,_⟩ := Periodic.isMinimizerAt_boundary_stability hV' hE hmin
  obtain ⟨N,hN,hp,hae,_⟩ := isMinimizerAt_stationary_tubular_normal hV' hE hmin hμ hCMC
  obtain ⟨b,hsg⟩ := isMinimizerAt_nonstandard_strict_signs_of_actual_normal hV hE hmin hc hstd hR hμ hN hp hae
  have hH := Periodic.coordinateCMC_of_global hμ hCMC
  have hn (i : Fin 3) := strict_normal_component_ne_zero_ae hV' hE hmin hR hμ hH hN hp hae hsg i
  exact ⟨μ,hμ,hn,fun i ↦ axialAreaMarginal_absolutelyContinuous hH hn i⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev TransverseProduct := Fin 2 → AxisCircle

def torusAxialSplit (i : Fin 3) : Torus ≃ᵐ AxisCircle × TransverseProduct :=
  (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ AxisCircle)).toMeasurableEquiv.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ AxisCircle) i)

lemma torusAxialSplit_measurePreserving (i : Fin 3) :
    MeasurePreserving (torusAxialSplit i) torusVolume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ AxisCircle) i).comp
    torus_to_product_measurePreserving

lemma torusAxialSplit_fst (i : Fin 3) (z : Torus) : (torusAxialSplit i z).1=z i := rfl

lemma torusAxialSplit_symm_apply (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    (torusAxialSplit i).symm (t,y)=WithLp.toLp 2 (i.insertNth t y) := rfl

@[simp] lemma torusAxialSplit_symm_same (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    ((torusAxialSplit i).symm (t,y)) i=t := by
  change i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) t y i=t
  exact Fin.insertNth_apply_same (α := fun _ : Fin 3 ↦ AxisCircle) i t y

@[simp] lemma torusAxialSplit_symm_succAbove (i : Fin 3) (t : AxisCircle)
    (y : TransverseProduct) (j : Fin 2) :
    ((torusAxialSplit i).symm (t,y)) (i.succAbove j)=y j := by
  change i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) t y (i.succAbove j)=y j
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 ↦ AxisCircle) i t y j

def axialSlice (E : Set Torus) (i : Fin 3) (t : AxisCircle) : Set TransverseProduct :=
  {y | (torusAxialSplit i).symm (t,y)∈E}

def axialSliceVolume (E : Set Torus) (i : Fin 3) (t : AxisCircle) : ℝ≥0∞ :=
  volume (axialSlice E i t)

lemma axialSlice_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) (t : AxisCircle) :
    MeasurableSet (axialSlice E i t) :=
  hE.preimage ((torusAxialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id))

lemma axialSliceVolume_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    Measurable (axialSliceVolume E i) := by
  exact measurable_measure_prodMk_left (hE.preimage (torusAxialSplit i).symm.measurable)

lemma axialSliceVolume_le_one (E : Set Torus) (i : Fin 3) (t : AxisCircle) :
    axialSliceVolume E i t≤1 := by
  exact (measure_mono (subset_univ _)).trans_eq (measure_univ : volume (univ : Set TransverseProduct)=1)

lemma axialSliceVolume_lintegral {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    (∫⁻ t,axialSliceVolume E i t)=torusVolume E := by
  have hh := (torusAxialSplit_measurePreserving i).symm.measure_preimage hE.nullMeasurableSet
  change (volume.prod volume) ((torusAxialSplit i).symm ⁻¹' E)=torusVolume E at hh
  rw [Measure.prod_apply (hE.preimage (torusAxialSplit i).symm.measurable)] at hh
  exact hh

lemma axialVolumeMarginal_apply {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {s : Set AxisCircle} (hs : MeasurableSet s) :
    (axialVolumeMarginal E i : Measure AxisCircle) s=torusVolume (E∩{z : Torus | z i∈s}) := by
  have hm : Measurable (fun x : Cover ↦ (x i : AxisCircle)) :=
    (cube_axis_measurePreserving i).measurable
  change Measure.map _ _ s=_
  rw [Measure.map_apply hm hs,Measure.restrict_apply (hs.preimage hm)]
  have he : (fun x : Cover ↦ (x i : AxisCircle)) ⁻¹' s∩(fundamentalCube∩quotientMap ⁻¹' E)=
      quotientMap ⁻¹' (E∩{z : Torus | z i∈s})∩fundamentalCube := by
    ext x; simp only [mem_preimage,mem_inter_iff,mem_ofPred_eq]; tauto
  rw [he]
  have hS : MeasurableSet (E∩{z : Torus | z i∈s}) := hE.inter
    (hs.preimage (torus_axis_measurePreserving i).measurable)
  have hh := quotientMap_measurePreserving.measure_preimage hS.nullMeasurableSet
  rw [Measure.restrict_apply (hS.preimage continuous_quotientMap.measurable)] at hh
  exact hh

theorem axialVolumeMarginal_eq_withDensity {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    (axialVolumeMarginal E i : Measure AxisCircle)=volume.withDensity (axialSliceVolume E i) := by
  apply Measure.ext
  intro s hs
  rw [axialVolumeMarginal_apply hE i hs,withDensity_apply _ hs]
  have hS : MeasurableSet (E∩{z : Torus | z i∈s}) := hE.inter
    (hs.preimage (torus_axis_measurePreserving i).measurable)
  rw [←(torusAxialSplit_measurePreserving i).symm.measure_preimage hS.nullMeasurableSet]
  change (volume.prod volume) ((torusAxialSplit i).symm ⁻¹' (E∩{z : Torus | z i∈s}))=_
  rw [Measure.prod_apply (hS.preimage (torusAxialSplit i).symm.measurable),←lintegral_indicator hs]
  apply lintegral_congr
  intro t
  by_cases ht : t∈s
  · rw [indicator_of_mem ht]
    congr 1
    ext y
    simp [axialSlice,ht]
  · rw [indicator_of_notMem ht]
    have he : Prod.mk t ⁻¹' ((torusAxialSplit i).symm ⁻¹' (E∩{z : Torus | z i∈s}))=∅ := by
      ext y; simp [ht]
    rw [he,measure_empty]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialPlanePoint (i : Fin 3) (t : ℝ) (y : Plane) : Cover :=
  WithLp.toLp 2 (i.insertNth t y)

lemma axialPlanePoint_dist (i : Fin 3) (t : ℝ) (x y : Plane) :
    dist (axialPlanePoint i t x) (axialPlanePoint i t y)=dist x y := by
  simp only [dist_eq_norm]
  have hs : ‖axialPlanePoint i t x-axialPlanePoint i t y‖^2=‖x-y‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succAbove _ i]
    simp [axialPlanePoint,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  nlinarith [norm_nonneg (axialPlanePoint i t x-axialPlanePoint i t y),norm_nonneg (x-y)]

lemma axialPlanePoint_continuous (i : Fin 3) (t : ℝ) : Continuous (axialPlanePoint i t) :=
  (Isometry.of_dist_eq (axialPlanePoint_dist i t)).continuous

lemma axialPlane_local_antilipschitz (i : Fin 3) (t : ℝ) (a : Plane) :
    AntilipschitzWith 1 (fun y : ball a (1/8 : ℝ) ↦ quotientMap (axialPlanePoint i t y)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one,one_mul,Subtype.dist_eq]
  have hs : ‖axialPlanePoint i t x-axialPlanePoint i t y‖<1/2 := by
    rw [←dist_eq_norm,axialPlanePoint_dist]
    exact (dist_triangle (x : Plane) a (y : Plane)).trans_lt (by have hy := y.property; rw [mem_ball,dist_comm] at hy; linarith [show dist (x : Plane) a<1/8 from x.property])
  have he : dist (quotientMap (axialPlanePoint i t x)) (quotientMap (axialPlanePoint i t y))=
      dist (axialPlanePoint i t x) (axialPlanePoint i t y) := by
    rw [dist_eq_norm,←quotientMap_sub,←norm_shortestLift,shortestLift_quotientMap hs,dist_eq_norm]
  rw [he,axialPlanePoint_dist]

lemma axialPlane_preimage_hausdorff_null (i : Fin 3) (t : ℝ) {S : Set Torus}
    (hS : Measure.hausdorffMeasure 2 S=0) :
    (volume : Measure Plane) ((fun y ↦ quotientMap (axialPlanePoint i t y)) ⁻¹' S)=0 := by
  let f : Plane → Torus := fun y ↦ quotientMap (axialPlanePoint i t y)
  have hl (a : Plane) : volume (f ⁻¹' S∩ball a (1/8 : ℝ))=0 := by
    have hh := (axialPlane_local_antilipschitz i t a).hausdorffMeasure_preimage_le (by norm_num : (0 : ℝ)≤2) S
    have hz : Measure.hausdorffMeasure 2 ((fun y : ball a (1/8 : ℝ) ↦ f y) ⁻¹' S)=0 := by
      apply le_zero_iff.mp
      simpa [hS] using hh
    have he := (isometry_subtype_coe : Isometry (Subtype.val : ball a (1/8 : ℝ) → Plane)).hausdorffMeasure_image
      (Or.inl (by norm_num : (0 : ℝ)≤2)) ((fun y : ball a (1/8 : ℝ) ↦ f y) ⁻¹' S)
    have ht : Subtype.val '' ((fun y : ball a (1/8 : ℝ) ↦ f y) ⁻¹' S)=f ⁻¹' S∩ball a (1/8 : ℝ) := by
      ext y; simp only [mem_image,mem_preimage,mem_inter_iff]; constructor
      · rintro ⟨z,hz,rfl⟩; exact ⟨hz,z.property⟩
      · rintro ⟨hy,hb⟩; exact ⟨⟨y,hb⟩,hy,rfl⟩
    rw [ht,hz] at he
    exact Measure.absolutelyContinuous_isAddHaarMeasure (volume : Measure Plane) (Measure.hausdorffMeasure 2) he
  obtain ⟨D,hD,hDD⟩ := TopologicalSpace.exists_countable_dense Plane
  have hc : ⋃ a∈D,ball a (1/8 : ℝ)=univ := (dense_iff_iUnion_ball D).mp hDD _ (by norm_num)
  have he : f ⁻¹' S=⋃ a∈D,f ⁻¹' S∩ball a (1/8 : ℝ) := by
    rw [←inter_iUnion₂,hc,inter_univ]
  rw [he]
  exact measure_biUnion_null_iff hD |>.mpr (fun a _ ↦ hl a)

lemma transverse_quotient_measurePreserving :
    MeasurePreserving (fun y : Fin 2 → ℝ ↦ fun j ↦ (y j : AxisCircle))
      ((volume : Measure (Fin 2 → ℝ)).restrict (univ.pi (fun _ ↦ Ico (0 : ℝ) 1))) volume := by
  have hh := measurePreserving_pi (fun _ : Fin 2 ↦ volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 2 ↦ (volume : Measure AxisCircle)) (fun _ ↦ circle_measurePreserving_mk_Ico)
  simpa only [volume_pi,Measure.restrict_pi_pi] using hh

lemma axialSlice_hausdorff_null (i : Fin 3) (t : AxisCircle) {S : Set Torus}
    (hSm : MeasurableSet S) (hS : Measure.hausdorffMeasure 2 S=0) : volume (axialSlice S i t)=0 := by
  induction t using Quotient.inductionOn with | h t =>
    have hp := axialPlane_preimage_hausdorff_null i t hS
    have he : (fun y : Fin 2 → ℝ ↦ (torusAxialSplit i).symm ((t : AxisCircle),fun j ↦ (y j : AxisCircle)))=
        (fun y : Plane ↦ quotientMap (axialPlanePoint i t y)) ∘ (WithLp.toLp 2) := by
      funext y
      apply PiLp.ext
      refine (Fin.forall_iff_succAbove i).mpr ⟨?_,?_⟩
      · simp [axialPlanePoint,torusAxialSplit_symm_apply,quotientMap]
      · intro j; simp [axialPlanePoint,torusAxialSplit_symm_apply,quotientMap]
    have hnull : volume ((fun y : Fin 2 → ℝ ↦ (torusAxialSplit i).symm ((t : AxisCircle),fun j ↦ (y j : AxisCircle))) ⁻¹' S)=0 := by
      rw [he,preimage_comp]
      exact (PiLp.volume_preserving_toLp (Fin 2)).quasiMeasurePreserving.preimage_null hp
    rw [←transverse_quotient_measurePreserving.map_eq,
      Measure.map_apply transverse_quotient_measurePreserving.measurable (axialSlice_measurable hSm i (t : AxisCircle))]
    exact le_zero_iff.mp ((Measure.restrict_le_self _) |>.trans_eq hnull)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_component_abs_le_one (ν : NormalSphere) (i : Fin 3) :
    |(ν : Cover) i|≤1 := by
  have hh := normalSphere_coordinate_sq_le ν i
  nlinarith [sq_abs ((ν : Cover) i),abs_nonneg ((ν : Cover) i)]

def axialPositiveFluxMarginal (μ : FiniteMeasure NormalBundle) (i : Fin 3) : FiniteMeasure AxisCircle := by
  let w : NormalBundle → ℝ := fun z ↦ 1+((z.2 : Cover) i)
  have hi : Integrable w (μ : Measure NormalBundle) :=
    (continuous_const.add (normal_component_continuous i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let η := (μ : Measure NormalBundle).withDensity (fun z ↦ ENNReal.ofReal (w z))
  haveI : IsFiniteMeasure η := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  exact ⟨Measure.map (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) η,inferInstance⟩

lemma axialPositiveFluxMarginal_absolutelyContinuous {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (axialPositiveFluxMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hh := ha hz
  change Measure.map _ _ s=0 at hh ⊢
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh ⊢
  exact withDensity_absolutelyContinuous _ _ hh

lemma axialPositiveFluxMarginal_integral (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialPositiveFluxMarginal μ i : Measure AxisCircle))=
      ∫ z,(1+((z.2 : Cover) i))*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
  have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1+((z.2 : Cover) i))) :=
    (continuous_const.add (normal_component_continuous i)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (by have hh := (abs_le.mp (normal_component_abs_le_one z.2 i)).1; linarith),smul_eq_mul]

lemma axialAreaMarginal_integral (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialAreaMarginal μ i : Measure AxisCircle))=
      ∫ z,f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  exact integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable

def axialNormalDensity (μ : FiniteMeasure NormalBundle) (i : Fin 3) (t : AxisCircle) : ℝ :=
  ((axialPositiveFluxMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal-
    ((axialAreaMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal

lemma axialNormalDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialNormalDensity μ i) :=
  Measure.integrable_toReal_rnDeriv.sub Measure.integrable_toReal_rnDeriv

lemma axialNormalDensity_measurable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Measurable (axialNormalDensity μ i) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal.sub (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma axialNormalDensity_pairing {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,axialNormalDensity μ i t*f t)=
      ∫ z,((z.2 : Cover) i)*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  have hp := axialPositiveFluxMarginal_absolutelyContinuous i ha
  have hi (η : FiniteMeasure AxisCircle) : Integrable f (η : Measure AxisCircle) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi' : Integrable (fun z : NormalBundle ↦ f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
    (hf.comp (normal_axisCircle_continuous i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi'' : Integrable (fun z : NormalBundle ↦ (1+((z.2 : Cover) i))*f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
    ((continuous_const.add (normal_component_continuous i)).mul (hf.comp (normal_axisCircle_continuous i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [axialNormalDensity,sub_mul]
  rw [integral_sub ((integrable_toReal_rnDeriv_mul_iff hp).mpr (hi _))
    ((integrable_toReal_rnDeriv_mul_iff ha).mpr (hi _)),
    integral_toReal_rnDeriv_mul hp,integral_toReal_rnDeriv_mul ha,
    axialPositiveFluxMarginal_integral μ i hf,axialAreaMarginal_integral μ i hf,←integral_sub hi'' hi']
  apply integral_congr_ae
  filter_upwards [] with z
  ring

lemma axialSliceVolume_real_integrable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    Integrable (fun t ↦ (axialSliceVolume E i t).toReal) := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (axialSliceVolume_measurable hE i).ennreal_toReal.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using axialSliceVolume_le_one E i t)

theorem axialSliceVolume_weak_derivative {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1) :
    (∫ t,axialNormalDensity μ i t*hp.lift t)=
      ∫ t,(axialSliceVolume E i t).toReal*(real_periodic_deriv hp).lift t := by
  rw [axialNormalDensity_pairing i ha (continuous_periodic_lift hp hψ.continuous)]
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ ψ (x i) • (EuclideanSpace.single i 1 : Cover)) :=
    (hψ.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).smul contDiff_const
  have hFp : ∀ m x,ψ ((x+latticeVector m) i) • (EuclideanSpace.single i 1 : Cover)=ψ (x i) • EuclideanSpace.single i 1 :=
    fun m x ↦ by rw [axial_scalar_periodic hp i m x]
  obtain ⟨M,_,hM⟩ := periodic_bounded hF.continuous hFp
  have hh := normalMeasure_flux hμ hF hFp (show 0<M+1 by linarith [hM 0])
    (fun x ↦ (hM x).trans (by linarith : M≤M+1))
  simp only [normalTest,ContinuousMap.coe_mk,real_inner_smul_right,EuclideanSpace.inner_single_right,
    axial_field_divergence (hψ.differentiable (by simp))] at hh
  have hd := continuous_periodic_lift (real_periodic_deriv hp) (hψ.continuous_deriv (by simp))
  have hvol := axialVolumeMarginal_integral E i hd
  rw [axialVolumeMarginal_eq_withDensity hE i,
    integral_withDensity_eq_integral_toReal_smul (axialSliceVolume_measurable hE i)
      (ae_of_all _ fun t ↦ lt_of_le_of_lt (axialSliceVolume_le_one E i t) ENNReal.one_lt_top)] at hvol
  simp only [smul_eq_mul,Function.Periodic.lift_coe] at hvol ⊢
  rw [hvol]
  simp only [starRingEnd_apply,star_trivial,one_mul] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [] with z
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circle_integrable_mul_continuous {h f : AxisCircle → ℝ} (hi : Integrable h)
    (hf : Continuous f) : Integrable (fun t ↦ h t*f t) := by
  let F : C(AxisCircle,ℝ) := ⟨f,hf⟩
  exact hi.mul_bdd hf.aestronglyMeasurable (ae_of_all _ fun t ↦ F.norm_coe_le_norm t)

lemma circle_integral_eq_interval {f : AxisCircle → ℝ} (hf : AEStronglyMeasurable f volume) :
    (∫ t,f t)=∫ t in (0 : ℝ)..1,f (t : AxisCircle) := by
  have hm : Measurable (fun t : ℝ ↦ (t : AxisCircle)) := (AddCircle.continuous_mk' (1 : ℝ)).measurable
  have hh := congrArg (fun η : Measure AxisCircle ↦ ∫ t,f t ∂η) axisCircleLebesgue_eq_volume
  change (∫ t,f t ∂Measure.map _ _)=_ at hh
  have hf' : AEStronglyMeasurable f (Measure.map (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1))) := by
    change AEStronglyMeasurable f (axisCircleLebesgue : Measure AxisCircle)
    rwa [axisCircleLebesgue_eq_volume]
  rw [integral_map hm.aemeasurable hf'] at hh
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
  exact hh.symm

lemma circle_intervalIntegrable {f : AxisCircle → ℝ} (hf : Integrable f volume) :
    IntervalIntegrable (fun t : ℝ ↦ f (t : AxisCircle)) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
  exact ((show MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1)) volume from
    by simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0).integrable_comp hf.aestronglyMeasurable).mpr hf

lemma circle_lift_smoothing_integral_tendsto {h : AxisCircle → ℝ} (hi : Integrable h)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    let F : ℝ → ℝ := fun t ↦ f (t : AxisCircle)
    let hp : Function.Periodic F 1 := fun t ↦ by dsimp only [F]; rw [AddCircle.coe_add_period]
    Tendsto (fun n ↦ ∫ t,h t*(circleSmoothApprox_periodic hp n).lift t) atTop
      (𝓝 (∫ t,h t*f t)) := by
  intro F hp
  have hF : Continuous F := hf.comp (AddCircle.continuous_mk' (1 : ℝ))
  obtain ⟨C,hC⟩ := (isCompact_univ.image hf).isBounded.exists_norm_le
  have hb (t : AxisCircle) : ‖f t‖≤C := hC _ ⟨t,mem_univ _,rfl⟩
  have hb' (t : ℝ) : ‖F t‖≤C := hb _
  apply tendsto_integral_of_dominated_convergence (fun t ↦ ‖h t‖*C)
  · intro n
    exact hi.aestronglyMeasurable.mul (continuous_periodic_lift (circleSmoothApprox_periodic hp n)
      (circleSmoothApprox_contDiff hF n).continuous).aestronglyMeasurable
  · exact hi.norm.mul_const C
  · intro n
    filter_upwards [] with t
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    induction t using Quotient.inductionOn with | h t =>
      exact circleSmoothApprox_bound hb' n t
  · filter_upwards [] with t
    induction t using Quotient.inductionOn with | h t =>
      exact tendsto_const_nhds.mul (circleSmoothApprox_tendsto hF t)

lemma integrable_circle_eq_zero_of_continuous_pairing {h : AxisCircle → ℝ}
    (hm : Measurable h) (hi : Integrable h)
    (hz : ∀ f : AxisCircle → ℝ,Continuous f → (∫ t,h t*f t)=0) : h=ᵐ[volume]0 := by
  let η := volume.withDensity (fun t ↦ ENNReal.ofReal (h t))
  let θ := volume.withDensity (fun t ↦ ENNReal.ofReal (-h t))
  have : IsFiniteMeasure η := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  have : IsFiniteMeasure θ := isFiniteMeasure_withDensity_ofReal hi.neg.hasFiniteIntegral
  have he : η=θ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    change (∫ t,f t ∂volume.withDensity _)=(∫ t,f t ∂volume.withDensity _)
    rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul (show Measurable (fun t ↦ ENNReal.ofReal (-h t)) from hm.neg.ennreal_ofReal) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal',smul_eq_mul]
    have hip : Integrable (fun t ↦ max (h t) 0*f t) := by
      exact circle_integrable_mul_continuous (hi.sup (integrable_const (0 : ℝ))) f.continuous
    have hin : Integrable (fun t ↦ max (-h t) 0*f t) := by
      exact circle_integrable_mul_continuous (hi.neg.sup (integrable_const (0 : ℝ))) f.continuous
    apply sub_eq_zero.mp
    rw [←integral_sub hip hin]
    convert hz f f.continuous using 1
    apply integral_congr_ae
    filter_upwards [] with t
    rcases le_total 0 (h t) with ht|ht
    · rw [max_eq_left ht,max_eq_right (neg_nonpos.mpr ht),zero_mul,sub_zero]
    · rw [max_eq_right ht,max_eq_left (neg_nonneg.mpr ht),zero_mul,zero_sub]; ring
  have hae := (withDensity_eq_iff_of_sigmaFinite hm.ennreal_ofReal.aemeasurable hm.neg.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [hae] with t ht
  have hh := congrArg ENNReal.toReal ht
  simp only [ENNReal.toReal_ofReal',Pi.neg_apply] at hh
  change h t=0
  rcases le_total 0 (h t) with hle|hle
  · rw [max_eq_left hle,max_eq_right (neg_nonpos.mpr hle)] at hh; exact hh
  · rw [max_eq_right hle,max_eq_left (neg_nonneg.mpr hle)] at hh; linarith

theorem integrable_circle_constant_of_weak_derivative_zero {h : AxisCircle → ℝ}
    (hm : Measurable h) (hi : Integrable h)
    (hw : ∀ (ψ : ℝ → ℝ) (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1),
      (∫ t,h t*(real_periodic_deriv hp).lift t)=0) :
    h=ᵐ[volume](fun _ ↦ ∫ t,h t) := by
  let c : ℝ := ∫ t,h t
  have hs : ∀ (f : ℝ → ℝ),ContDiff ℝ (⊤ : ℕ∞) f → ∀ hp : Function.Periodic f 1,
      (∫ t,(h t-c)*hp.lift t)=0 := by
    intro f hf hp
    obtain ⟨ψ,hψ,hψp,hd⟩ := smooth_periodic_centered_primitive hf hp
    have he : (real_periodic_deriv hψp).lift=(fun t : AxisCircle ↦ hp.lift t-∫ u in (0 : ℝ)..1,f u) := by
      funext t
      induction t using Quotient.inductionOn with | h t => exact hd t
    have hh := hw ψ hψ hψp
    rw [he] at hh
    have hfi : Integrable hp.lift := (continuous_periodic_lift hp hf.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hhi : Integrable (fun t ↦ h t*hp.lift t) := circle_integrable_mul_continuous hi (continuous_periodic_lift hp hf.continuous)
    simp only [mul_sub] at hh
    rw [integral_sub hhi (hi.mul_const _),integral_mul_const] at hh
    simp only [sub_mul]
    rw [integral_sub hhi (hfi.const_mul c),integral_const_mul]
    have hfint : (∫ t,hp.lift t)=∫ t in (0 : ℝ)..1,f t := by
      simpa only [Function.Periodic.lift_coe] using circle_integral_eq_interval hfi.aestronglyMeasurable
    rw [hfint]
    dsimp only [c]
    linarith
  have hz : ∀ f : AxisCircle → ℝ,Continuous f → (∫ t,(h t-c)*f t)=0 := by
    intro f hf
    have ht := circle_lift_smoothing_integral_tendsto (hi.sub (integrable_const c)) hf
    apply tendsto_nhds_unique ht
    apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    exact (hs _ (circleSmoothApprox_contDiff (hf.comp (AddCircle.continuous_mk' (1 : ℝ))) n) _).symm
  have hz' := integrable_circle_eq_zero_of_continuous_pairing (hm.sub measurable_const)
    (hi.sub (integrable_const c)) hz
  filter_upwards [hz'] with t ht
  exact sub_eq_zero.mp ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma interval_primitive_absolutelyContinuous {g : ℝ → ℝ}
    (hi : ∀ a b,IntervalIntegrable g volume a b) (a b c : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ s in c..t,g s) a b := by
  have he : (fun t ↦ ∫ s in c..t,g s)=(fun t ↦ (∫ s in c..a,g s)+(∫ s in a..t,g s)) := by
    funext t
    exact (intervalIntegral.integral_add_adjacent_intervals (hi c a) (hi a t)).symm
  rw [he]
  exact (show ContDiff ℝ 1 (fun _ : ℝ ↦ ∫ s in c..a,g s) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval.add
    ((hi a b).absolutelyContinuousOnInterval_intervalIntegral (by simp))

lemma circle_ac_primitive {g : AxisCircle → ℝ} (hi : Integrable g) (hz : (∫ t,g t)=0) :
    ∃ (P : ℝ → ℝ) (hp : Function.Periodic P 1),Continuous P ∧
      (∀ a b,AbsolutelyContinuousOnInterval P a b) ∧
      (∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt P (g (t : AxisCircle)) t) ∧
      ∀ (ψ : ℝ → ℝ) (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : Function.Periodic ψ 1),
        (∫ t,hp.lift t*(real_periodic_deriv hψp).lift t)=-(∫ t,g t*hψp.lift t) := by
  let G : ℝ → ℝ := fun t ↦ g (t : AxisCircle)
  have hGp : Function.Periodic G 1 := fun t ↦ by dsimp only [G]; rw [AddCircle.coe_add_period]
  have hGi (a b : ℝ) : IntervalIntegrable G volume a b :=
    hGp.intervalIntegrable₀ (by norm_num) (circle_intervalIntegrable hi) a b
  let P : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t,G s
  have hPc : Continuous P := intervalIntegral.continuous_primitive hGi 0
  have hP0 : P 0=0 := intervalIntegral.integral_same
  have hP1 : P 1=0 := (circle_integral_eq_interval hi.aestronglyMeasurable).symm.trans hz
  have hPp : Function.Periodic P 1 := by
    intro t
    change (∫ s in (0 : ℝ)..t+1,G s)=∫ s in (0 : ℝ)..t,G s
    rw [hGp.intervalIntegral_add_eq_add 0 t hGi]
    rw [zero_add]
    change P t+P 1=P t
    rw [hP1,add_zero]
  have hPac (a b : ℝ) : AbsolutelyContinuousOnInterval P a b :=
    interval_primitive_absolutelyContinuous hGi a b 0
  have hPd : ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt P (G t) t := by
    filter_upwards [(hGi 0 1).ae_hasDerivAt_integral] with t ht hti
    exact ht (by simpa using hti) 0 (by simp)
  refine ⟨P,hPp,hPc,hPac,hPd,?_⟩
  intro ψ hψ hψp
  have hψc := continuous_periodic_lift hψp hψ.continuous
  have hdc := continuous_periodic_lift (real_periodic_deriv hψp) (hψ.continuous_deriv (by simp))
  have hPc' := continuous_periodic_lift hPp hPc
  rw [circle_integral_eq_interval (show AEStronglyMeasurable (fun t ↦ hPp.lift t*(real_periodic_deriv hψp).lift t) volume from (hPc'.mul hdc).aestronglyMeasurable),
    circle_integral_eq_interval (circle_integrable_mul_continuous hi hψc).aestronglyMeasurable]
  simp only [Function.Periodic.lift_coe]
  have hparts := (hPac 0 1).integral_mul_deriv_eq_deriv_mul
    (hψ.of_le (by simp) : ContDiff ℝ 1 ψ).contDiffOn.absolutelyContinuousOnInterval
  rw [hP1,hP0,zero_mul,zero_mul,sub_self,zero_sub] at hparts
  rw [hparts]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hPd] with t ht hti
  rw [(ht (by simpa using uIoc_subset_uIcc hti)).deriv]

theorem circle_weak_integrable_has_ac_representative {u g : AxisCircle → ℝ}
    (hu : Measurable u) (hui : Integrable u) (hgi : Integrable g)
    (hw : ∀ (ψ : ℝ → ℝ) (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1),
      (∫ t,g t*hp.lift t)=(∫ t,u t*(real_periodic_deriv hp).lift t)) :
    ∃ (f : ℝ → ℝ) (hp : Function.Periodic f 1),Continuous f ∧
      (∀ a b,AbsolutelyContinuousOnInterval f a b) ∧ u=ᵐ[volume]hp.lift ∧
      ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt f (-g (t : AxisCircle)) t := by
  have hg0 : (∫ t,g t)=0 := by
    have hp : Function.Periodic (fun _ : ℝ ↦ (1 : ℝ)) 1 := fun _ ↦ rfl
    have hh := hw (fun _ ↦ 1) contDiff_const hp
    have he (t : AxisCircle) : hp.lift t=1 := by
      induction t using Quotient.inductionOn with | h t => rfl
    have hd (t : AxisCircle) : (real_periodic_deriv hp).lift t=0 := by
      induction t using Quotient.inductionOn with | h t => exact deriv_const t 1
    simpa only [he,hd,mul_one,mul_zero,integral_zero] using hh
  obtain ⟨P,hPp,hPc,hPac,hPd,hPw⟩ := circle_ac_primitive hgi hg0
  have hPlc := continuous_periodic_lift hPp hPc
  have hPi : Integrable hPp.lift := hPlc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hzero : ∀ (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1),
      (∫ t,(u t+hPp.lift t)*(real_periodic_deriv hp).lift t)=0 := by
    intro ψ hψ hp
    have hc := continuous_periodic_lift (real_periodic_deriv hp) (hψ.continuous_deriv (by simp))
    simp only [add_mul]
    rw [integral_add (circle_integrable_mul_continuous hui hc) (circle_integrable_mul_continuous hPi hc),
      hPw ψ hψ hp,hw ψ hψ hp,add_neg_cancel]
  let c := ∫ t,u t+hPp.lift t
  have hae := integrable_circle_constant_of_weak_derivative_zero (hu.add hPlc.measurable)
    (hui.add hPi) hzero
  let f : ℝ → ℝ := fun t ↦ c-P t
  have hfp : Function.Periodic f 1 := fun t ↦ by dsimp only [f]; rw [hPp t]
  refine ⟨f,hfp,continuous_const.sub hPc,?_,?_,?_⟩
  · intro a b
    exact (show ContDiff ℝ 1 (fun _ : ℝ ↦ c) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval.sub (hPac a b)
  · filter_upwards [hae] with t ht
    have he : hfp.lift t=c-hPp.lift t := by
      induction t using Quotient.inductionOn with | h t => rfl
    rw [he]
    change u t+hPp.lift t=c at ht
    linarith
  · filter_upwards [hPd] with t ht hti
    exact (ht hti).const_sub c

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSlice_point_continuous (i : Fin 3) (y : TransverseProduct) :
    Continuous (fun t : AxisCircle ↦ (torusAxialSplit i).symm (t,y)) := by
  change Continuous (fun t : AxisCircle ↦ WithLp.toLp 2 (i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) t y))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  exact (Fin.forall_iff_succAbove (P := fun j : Fin 3 ↦ Continuous (fun t : AxisCircle ↦ (i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) t y) j)) i).mpr ⟨by simp only [Fin.insertNth_apply_same]; exact continuous_id,fun k ↦ by simp only [Fin.insertNth_apply_succAbove]; exact continuous_const⟩ j

lemma isMinimizerAt_boundary_slice_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) (t : AxisCircle) :
    volume (axialSlice (frontier (openRepresentative E)) i t)=0 := by
  let T : Set Torus := {z | z i=t}
  have hT : MeasurableSet T := measurableSet_eq_fun (torus_axis_measurePreserving i).measurable measurable_const
  have ht : (spatialNormalMeasure μ : Measure Torus) T=0 := by
    have hh := ha (axisCircle_singleton_null t)
    change Measure.map _ _ {t}=0 at hh
    rw [Measure.map_apply (normal_axisCircle_continuous i).measurable (measurableSet_singleton t)] at hh
    change Measure.map normalProjection _ T=0
    rw [Measure.map_apply normalProjection_continuous.measurable hT]
    exact hh
  have hh := isMinimizerAt_boundary_area_absolutelyContinuous hV hE hmin hμ ht
  rw [Measure.restrict_apply hT] at hh
  have hs := axialSlice_hausdorff_null i t (hT.inter isClosed_frontier.measurableSet) hh
  have he : axialSlice (T∩frontier (openRepresentative E)) i t=axialSlice (frontier (openRepresentative E)) i t := by
    ext y
    simp [axialSlice,T]
  rwa [he] at hs

lemma axialSliceVolume_continuous_of_boundary_null {U : Set Torus} (hU : MeasurableSet U)
    (i : Fin 3) (hn : ∀ t : AxisCircle,volume (axialSlice (frontier U) i t)=0) :
    Continuous (fun t ↦ (axialSliceVolume U i t).toReal) := by
  let F : AxisCircle → TransverseProduct → ℝ := fun t y ↦ U.indicator (fun _ ↦ (1 : ℝ)) ((torusAxialSplit i).symm (t,y))
  have he (t : AxisCircle) : (∫ y,F t y)=(axialSliceVolume U i t).toReal := by
    have hf : F t=(axialSlice U i t).indicator 1 := by
      funext y
      by_cases hy : (torusAxialSplit i).symm (t,y)∈U <;> simp [F,axialSlice,hy]
    rw [hf,integral_indicator_one (axialSlice_measurable hU i t)]
    rfl
  rw [show (fun t ↦ (axialSliceVolume U i t).toReal)=(fun t ↦ ∫ y,F t y) from funext (fun t ↦ (he t).symm)]
  apply continuous_iff_continuousAt.mpr
  intro t
  apply continuousAt_of_dominated (bound := fun _ ↦ (1 : ℝ))
  · apply Eventually.of_forall
    intro s
    exact (measurable_const.indicator hU |>.comp ((torusAxialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro s
    apply ae_of_all
    intro y
    exact (norm_indicator_le_norm_self (s := U) (fun _ ↦ (1 : ℝ)) ((torusAxialSplit i).symm (s,y))).trans (by norm_num)
  · exact integrable_const 1
  · have hnb : ∀ᵐ y : TransverseProduct,(torusAxialSplit i).symm (t,y)∉frontier U := by
      rw [ae_iff]
      simpa only [not_not,axialSlice] using hn t
    filter_upwards [hnb] with y hy
    change ContinuousAt (fun s ↦ U.indicator (fun _ ↦ (1 : ℝ)) ((torusAxialSplit i).symm (s,y))) t
    exact ContinuousAt.comp (f := fun s ↦ (torusAxialSplit i).symm (s,y)) (g := U.indicator (fun _ ↦ (1 : ℝ))) (continuous_const.continuousOn.continuousAt_indicator hy) (axialSlice_point_continuous i y).continuousAt

theorem isMinimizerAt_nonstandard_slice_continuous {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∀ i : Fin 3,Continuous (fun t ↦ (axialSliceVolume (openRepresentative E) i t).toReal) := by
  obtain ⟨μ,hμ,_,ha⟩ := isMinimizerAt_nonstandard_area_marginals hV hE hmin hc hstd hR
  intro i
  exact axialSliceVolume_continuous_of_boundary_null (isOpen_openRepresentative E).measurableSet i
    (isMinimizerAt_boundary_slice_null ⟨hV.1,by linarith [hV.2]⟩ hE hmin hμ i (ha i))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def octantHeight (b : Fin 3 → Bool) (i : Fin 3) (t : ℝ) : ℝ :=
  if b i then (1+t)/2 else 1-t/2

lemma octantHeight_mem (b : Fin 3 → Bool) (i : Fin 3) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    octantHeight b i t∈Icc (1/2 : ℝ) 1 := by
  unfold octantHeight
  cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    constructor <;> linarith [ht.1,ht.2]

lemma upperFold_slice_same (i : Fin 3) {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1)
    (y : TransverseProduct) : upperFold ((torusAxialSplit i).symm ((t : AxisCircle),y)) i=t := by
  change 1-‖((torusAxialSplit i).symm ((t : AxisCircle),y)) i‖=t
  rw [torusAxialSplit_symm_same,circle_norm_upper ht]
  ring

lemma upperFold_slice_succAbove (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) (j : Fin 2) :
    upperFold ((torusAxialSplit i).symm (t,y)) (i.succAbove j)=1-‖y j‖ := by
  change 1-‖((torusAxialSplit i).symm (t,y)) (i.succAbove j)‖=1-‖y j‖
  rw [torusAxialSplit_symm_succAbove]

end CubicTorus
end
end
end

end OAI
