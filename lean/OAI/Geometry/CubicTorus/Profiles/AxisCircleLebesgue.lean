import Mathlib
import OAI.Geometry.CubicTorus.Profiles.OctantVertex

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axisCircleLebesgue : FiniteMeasure AxisCircle :=
  ⟨Measure.map (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1)),inferInstance⟩

lemma axialSurfaceMarginal_integral (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialSurfaceMarginal μ i : Measure AxisCircle))=
      ∫ z,f (((z.1 : Cover) i) : AxisCircle)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  have hc : Continuous (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.fst)
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable]
  have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1-((z.2 : Cover) i)^2)) :=
    (continuous_const.sub ((normal_component_continuous i).pow 2)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (normalSphere_coordinate_sq_le z.2 i)),smul_eq_mul,mul_comm]

lemma axialVolumeMarginal_integral (E : Set Torus) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialVolumeMarginal E i : Measure AxisCircle))=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i : AxisCircle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  have hc : Continuous (fun x : Cover ↦ (x i : AxisCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable]

lemma axisCircleLebesgue_integral {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axisCircleLebesgue : Measure AxisCircle))=
      ∫ t in (0 : ℝ)..1,f (t : AxisCircle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  have hc : Continuous (fun t : ℝ ↦ (t : AxisCircle)) := AddCircle.continuous_mk' (1 : ℝ)
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]

lemma axial_circle_flux_integral {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialSurfaceMarginal μ i : Measure AxisCircle))-
      H*(∫ t,f t ∂(axialVolumeMarginal E i : Measure AxisCircle))=
      (axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E))*
        (∫ t,f t ∂(axisCircleLebesgue : Measure AxisCircle)) := by
  rw [axialSurfaceMarginal_integral μ i hf,axialVolumeMarginal_integral E i hf,
    axisCircleLebesgue_integral hf]
  have hc : Continuous (fun t : ℝ ↦ f (t : AxisCircle)) := hf.comp (AddCircle.continuous_mk' (1 : ℝ))
  exact axial_flux_marginal_continuous hH i hc
    (fun t ↦ by change f ((t+1 : ℝ) : AxisCircle)=f (t : AxisCircle); rw [AddCircle.coe_add_period])

theorem axial_circle_flux_measure {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    let c := axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E)
    (axialSurfaceMarginal μ i : Measure AxisCircle)+
      Real.toNNReal (-H) • (axialVolumeMarginal E i : Measure AxisCircle)+
      Real.toNNReal (-c) • (axisCircleLebesgue : Measure AxisCircle)=
      Real.toNNReal H • (axialVolumeMarginal E i : Measure AxisCircle)+
      Real.toNNReal c • (axisCircleLebesgue : Measure AxisCircle) := by
  intro c
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hi (η : Measure AxisCircle) [IsFiniteMeasure η] : Integrable f η := f.integrable
  rw [integral_add_measure (hi _) (hi _),integral_add_measure (hi _) (hi _),
    integral_add_measure (hi _) (hi _)]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul,Real.coe_toNNReal']
  have hh := axial_circle_flux_integral hH i f.continuous
  change _-H*_=c*_ at hh
  have split (a : ℝ) : max a 0-max (-a) 0=a := by
    rcases le_total 0 a with ha|ha
    · simp only [max_eq_left ha,max_eq_right (neg_nonpos.mpr ha),sub_zero]
    · simp only [max_eq_right ha,max_eq_left (neg_nonneg.mpr ha),zero_sub,neg_neg]
  have hh' : (∫ t,f t ∂(axialSurfaceMarginal μ i : Measure AxisCircle))-
      H*(∫ t,f t ∂(axialVolumeMarginal E i : Measure AxisCircle))=
      c*(∫ t,f t ∂(axisCircleLebesgue : Measure AxisCircle)) := hh
  rw [←split H,←split c] at hh'
  linarith only [hh']

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisCircleLebesgue_eq_volume : (axisCircleLebesgue : Measure AxisCircle)=volume := by
  change Measure.map (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1))=volume
  exact (show MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle))
    (volume.restrict (Ioc 0 1)) volume from by simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq

lemma torus_axis_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Torus ↦ x i) torusVolume (volume : Measure AxisCircle) := by
  have he := measurePreserving_eval (fun _ : Fin 3 ↦ (volume : Measure AxisCircle)) i
  rw [←volume_pi] at he
  exact he.comp torus_to_product_measurePreserving

lemma cube_axis_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Cover ↦ (x i : AxisCircle))
      (volume.restrict fundamentalCube) volume :=
  (torus_axis_measurePreserving i).comp quotientMap_measurePreserving

lemma axialVolumeMarginal_le (E : Set Torus) (i : Fin 3) :
    (axialVolumeMarginal E i : Measure AxisCircle)≤volume := by
  change Measure.map (fun x : Cover ↦ (x i : AxisCircle))
    (volume.restrict (fundamentalCube∩quotientMap ⁻¹' E))≤volume
  rw [←(cube_axis_measurePreserving i).map_eq]
  exact Measure.map_mono (Measure.restrict_mono inter_subset_left le_rfl)
    (cube_axis_measurePreserving i).measurable

lemma axialVolumeMarginal_absolutelyContinuous (E : Set Torus) (i : Fin 3) :
    (axialVolumeMarginal E i : Measure AxisCircle)≪volume :=
  (axialVolumeMarginal_le E i).absolutelyContinuous

theorem axialSurfaceMarginal_absolutelyContinuous {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    (axialSurfaceMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hv := axialVolumeMarginal_absolutelyContinuous E i hz
  have hh := congrArg (fun η : Measure AxisCircle ↦ η s) (axial_circle_flux_measure hH i)
  simp only [Measure.add_apply,Measure.smul_apply,axisCircleLebesgue_eq_volume,hz,hv,smul_zero,
    add_zero] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_axisCircle_continuous (i : Fin 3) :
    Continuous (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.fst)

lemma axial_null_normal_sq {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    {s : Set AxisCircle} (hs : MeasurableSet s) (hz : volume s=0) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),(((z.1 : Cover) i) : AxisCircle)∈s →
      ((z.2 : Cover) i)^2=1 := by
  have hh := axialSurfaceMarginal_absolutelyContinuous hH i hz
  change Measure.map _ _ s=0 at hh
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh
  have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1-((z.2 : Cover) i)^2)) :=
    (continuous_const.sub ((normal_component_continuous i).pow 2)).measurable.ennreal_ofReal
  have ha : ∀ᵐ z ∂(μ : Measure NormalBundle).withDensity
      (fun z ↦ ENNReal.ofReal (1-((z.2 : Cover) i)^2)),
      (((z.1 : Cover) i) : AxisCircle)∉s := by
    rw [ae_iff]
    simpa only [not_not, Set.preimage] using hh
  have hb := (ae_withDensity_iff hw).mp ha
  filter_upwards [hb] with z he hz
  have hw0 : ENNReal.ofReal (1-((z.2 : Cover) i)^2)=0 := by
    by_contra hn
    exact he hn hz
  have hn := ENNReal.ofReal_eq_zero.mp hw0
  have hu := normalSphere_coordinate_sq_le z.2 i
  linarith

lemma normalSphere_two_sq_le (ν : NormalSphere) {i j : Fin 3} (hij : i≠j) :
    ((ν : Cover) i)^2+((ν : Cover) j)^2≤1 := by
  have ht : i∈({i,j} : Finset (Fin 3)) := by simp
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({i,j} : Finset (Fin 3))⊆Finset.univ from Finset.subset_univ _)
    (fun k _ _ ↦ sq_nonneg ((ν : Cover) k))
  simpa only [Finset.sum_pair hij,normalSphere_sum_sq] using hh

theorem normalMeasure_two_null_axes {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) {i j : Fin 3} (hij : i≠j)
    {s t : Set AxisCircle} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hs0 : volume s=0) (ht0 : volume t=0) :
    (μ : Measure NormalBundle) {z | (((z.1 : Cover) i) : AxisCircle)∈s ∧
      (((z.1 : Cover) j) : AxisCircle)∈t}=0 := by
  have ha : ∀ᵐ z ∂(μ : Measure NormalBundle),¬(
      (((z.1 : Cover) i) : AxisCircle)∈s ∧ (((z.1 : Cover) j) : AxisCircle)∈t) := by
    filter_upwards [axial_null_normal_sq hH i hs hs0,axial_null_normal_sq hH j ht ht0] with z hi hj
    rintro ⟨hzi,hzj⟩
    have hu := normalSphere_two_sq_le z.2 hij
    rw [hi hzi,hj hzj] at hu
    norm_num at hu
  simpa only [ae_iff,not_not] using ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def upperFold (z : Torus) : Cover := WithLp.toLp 2 (fun i ↦ 1-‖z i‖)

lemma upperFold_continuous : Continuous upperFold := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i ↦ continuous_const.sub ((PiLp.continuous_apply 2 _ i).norm)))

lemma upperFold_mem (z : Torus) : upperFold z∈closedUpperOctant := by
  intro i
  have hh := AddCircle.norm_le_half_period 1 (x := z i) (by norm_num)
  norm_num at hh
  change (1/2 : ℝ)≤1-‖z i‖ ∧ 1-‖z i‖≤1
  constructor <;> linarith [norm_nonneg (z i)]

lemma circle_norm_upper {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1) :
    ‖(t : AddCircle (1 : ℝ))‖=1-t := by
  have he : ((t-1 : ℝ) : AddCircle (1 : ℝ))=(t : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_sub,AddCircle.coe_period,sub_zero]
  have hh := (AddCircle.norm_coe_eq_abs_iff 1 (x := t-1) (by norm_num)).mpr (by
    rw [abs_of_nonpos (by linarith [ht.2] : t-1≤0)]
    norm_num
    linarith [ht.1])
  rw [he,abs_of_nonpos (by linarith [ht.2] : t-1≤0)] at hh
  linarith

lemma upperFold_quotient {x : Cover} (hx : x∈closedUpperOctant) :
    upperFold (quotientMap x)=x := by
  ext i
  change 1-‖(x i : AddCircle (1 : ℝ))‖=x i
  rw [circle_norm_upper (hx i)]
  ring

lemma upperFold_eq_flip (z : Torus) : upperFold z=
    octantFlipSet (Finset.univ.filter (fun i ↦ representative z i≤1/2)) (representative z) := by
  classical
  have hz := quotientMap_representative z
  ext i
  have he : ((representative z i : ℝ) : AddCircle (1 : ℝ))=z i := congrArg (fun z : Torus ↦ z i) hz
  have hr := representative_mem_fundamentalCube z i
  change 0≤representative z i ∧ representative z i<1 at hr
  change 1-‖z i‖=if i∈Finset.univ.filter (fun j ↦ representative z j≤1/2) then 1-representative z i else representative z i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hi : representative z i≤1/2
  · rw [ite_eq_left hi,←he]
    have hh := (AddCircle.norm_coe_eq_abs_iff 1 (x := representative z i) (by norm_num)).mpr (by
      rw [abs_of_nonneg hr.1]; norm_num; exact hi)
    rw [hh,abs_of_nonneg hr.1]
  · rw [ite_eq_right hi,←he,circle_norm_upper ⟨(not_le.mp hi).le,hr.2.le⟩]
    ring

lemma upperFold_phase {O : Set Torus}
    (hR : ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈O ↔ z∈O)
    (z : Torus) : quotientMap (upperFold z)∈O ↔ z∈O := by
  rw [upperFold_eq_flip,octantFlipSet_mem hR,quotientMap_representative]

theorem octant_downset_closure {O : Set Torus} (hO : IsOpen O)
    (hR : ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈O ↔ z∈O)
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈O → quotientMap x∈O)
    {x y : Cover} (hx : x∈closedUpperOctant) (hy : y∈closedUpperOctant)
    (hxy : OrientedCoordinateLE b x y) (hyO : quotientMap y∈closure O) :
    quotientMap x∈closure O := by
  let f : Torus → Cover := fun z ↦ WithLp.toLp 2 (fun i ↦
    if b i then min (x i) (upperFold z i) else max (x i) (upperFold z i))
  have hfc : Continuous (fun z ↦ quotientMap (f z)) := by
    apply continuous_quotientMap.comp
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    have hu := (PiLp.continuous_apply 2 _ i).comp upperFold_continuous
    cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
      first | exact continuous_const.max hu | exact continuous_const.min hu
  have hfmem (z : Torus) : f z∈closedUpperOctant := by
    intro i
    have hh := upperFold_mem z i
    change (1/2 : ℝ)≤(if b i then min (x i) (upperFold z i) else max (x i) (upperFold z i)) ∧
      (if b i then min (x i) (upperFold z i) else max (x i) (upperFold z i))≤1
    cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact ⟨(hx i).1.trans (le_max_left _ _),max_le (hx i).2 hh.2⟩
    · exact ⟨le_min (hx i).1 hh.1,(min_le_left _ _).trans (hx i).2⟩
  have hford (z : Torus) : OrientedCoordinateLE b (f z) (upperFold z) := by
    intro i
    change if b i then (if b i then min (x i) (upperFold z i) else max (x i) (upperFold z i))≤upperFold z i
      else upperFold z i≤(if b i then min (x i) (upperFold z i) else max (x i) (upperFold z i))
    cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact le_max_right _ _
    · exact min_le_right _ _
  have hclosure : closure O⊆(fun z ↦ quotientMap (f z)) ⁻¹' closure O := by
    apply closure_minimal _ (isClosed_closure.preimage hfc)
    intro z hz
    exact octant_downset_closed_endpoint hO hd (hfmem z) (upperFold_mem z) (hford z)
      ((upperFold_phase hR z).mpr hz)
  have he : f (quotientMap y)=x := by
    ext i
    change (if b i then min (x i) (upperFold (quotientMap y) i) else max (x i) (upperFold (quotientMap y) i))=x i
    rw [upperFold_quotient hy]
    have hh := hxy i
    cases h : b i <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    · exact max_eq_left hh
    · exact min_eq_left hh
  simpa only [mem_preimage,he] using hclosure hyO

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma orientedCoordinateLE_reverse (b : Fin 3 → Bool) (x y : Cover) :
    OrientedCoordinateLE (fun i ↦ !b i) x y ↔ OrientedCoordinateLE b y x := by
  constructor <;> intro h i <;> have hh := h i <;> cases hb : b i <;>
    simpa only [hb,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] using hh

theorem isMinimizerAt_closed_octant_order {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {x y : Cover} (hx : x∈closedUpperOctant) (hy : y∈closedUpperOctant)
    (hxy : OrientedCoordinateLE b x y) (hyO : quotientMap y∈openRepresentative E) :
    quotientMap x∈openRepresentative E := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin
  have hRc (i : Fin 3) : Eᶜ=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' Eᶜ) := (hR i).compl
  have hcl := isMinimizerAt_closure_openRepresentative_null hV hmin
  have hclc := isMinimizerAt_closure_openRepresentative_null hVc hmc
  have hdcomp : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE (fun i ↦ !b i) x y →
      quotientMap y∈openRepresentative Eᶜ →quotientMap x∈openRepresentative Eᶜ := by
    intro u hu v hv huv hvO
    simp only [openRepresentative,compl_compl,mem_compl_iff] at hvO ⊢
    intro hucl
    have hur : u∈closedUpperOctant := fun i ↦ ⟨(hu i).1.le,(hu i).2.le⟩
    have hvr : v∈closedUpperOctant := fun i ↦ ⟨(hv i).1.le,(hv i).2.le⟩
    have hh := octant_downset_closure (isOpen_openRepresentative E)
      (reflection_invariant_openRepresentative hmin.1.1 hR) hd hvr hur
      ((orientedCoordinateLE_reverse b u v).mp huv) (by rwa [hcl])
    rw [hcl] at hh
    exact hvO (by simpa only [compl_compl] using hh)
  by_contra hxo
  have hxcl : quotientMap x∈closure (openRepresentative Eᶜ) := by
    rw [hclc]
    simpa only [openRepresentative,mem_compl_iff,not_not] using hxo
  have hh := octant_downset_closure (isOpen_openRepresentative Eᶜ)
    (reflection_invariant_openRepresentative hmc.1.1 hRc) hdcomp hy hx
    ((orientedCoordinateLE_reverse b y x).mpr hxy) hxcl
  rw [hclc] at hh
  exact hyO hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma compact_smooth_cutoff {K U : Set Cover} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K⊆U) :
    ∃ φ : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ⊆U ∧ ∀ x∈K,∀ᶠ y in 𝓝 x,φ y=1 := by
  classical
  have hp (a : K) := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU.mem_nhds (hKU a.2))
  choose f hs hc hf hb hone using hp
  let W (a : K) : Set Cover := {x | (3/4 : ℝ)<f a x}
  have hW (a : K) : IsOpen (W a) := isOpen_lt continuous_const (hf a).continuous
  obtain ⟨s,hcover⟩ := hK.elim_finite_subcover W hW (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,by change (3/4 : ℝ)<f ⟨x,hx⟩ x; rw [hone]; norm_num⟩)
  let F : Cover → ℝ := fun y ↦ ∑ a∈s,f a y
  have hFc : HasCompactSupport F := by
    simpa only [F,←Finset.sum_apply] using (HasCompactSupport.finset_sum (s := s) (fun a _ ↦ hc a))
  have hsup : ∀ t : Finset K,tsupport (∑ a∈t,f a)⊆U := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact (tsupport_add _ _).trans (union_subset (hs a) ih)
  have hFs : tsupport F⊆U := by simpa only [F,←Finset.sum_apply] using hsup s
  let g : ℝ → ℝ := fun t ↦ Real.smoothTransition (2*t)
  have hg : g 0=0 := by simp only [g,mul_zero]; exact Real.smoothTransition.zero_of_nonpos le_rfl
  let φ : Cover → ℝ := g ∘ F
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    exact ContDiff.sum (fun a _ ↦ hf a)
  refine ⟨φ,(Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)).comp hF,
    hFc.comp_left hg,(tsupport_comp_subset hg F).trans hFs,?_⟩
  intro x hx
  obtain ⟨a,ha,hax⟩ := mem_iUnion₂.mp (hcover hx)
  have hnear : ∀ᶠ y in 𝓝 x,(1/2 : ℝ)<f a y :=
    (hf a).continuous.continuousAt.eventually_const_lt (by change (3/4 : ℝ)<f a x at hax; linarith)
  filter_upwards [hnear] with y hy
  have hsum : f a y≤F y := by
    change f a y≤∑ b∈s,f b y
    exact Finset.single_le_sum (fun b _ ↦ (hb b (mem_range_self y)).1) ha
  exact Real.smoothTransition.one_of_one_le (by linarith)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem exists_periodic_position (c : Cover) {K : Set Cover} (hK : IsCompact K)
    (hbox : ∀ x∈K,∀ i : Fin 3,c i-1/2<x i ∧ x i<c i+1/2) :
    ∃ X : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) X ∧
      (∀ m x,X (x+latticeVector m)=X x) ∧
      ∀ x∈K,X=ᶠ[𝓝 x](fun y ↦ y-c) := by
  let L : Set Cover := (fun x : Cover ↦ x-c+cubeCenter) '' K
  have hL : IsCompact L := hK.image ((continuous_id.sub continuous_const).add continuous_const)
  let U : Set Cover := {x | ∀ i : Fin 3,0<x i ∧ x i<1}
  have hU : IsOpen U := by
    have he : U=(⋂ i : Fin 3,{x : Cover | 0<x i ∧ x i<1}) := by ext x; simp [U]
    rw [he]
    exact isOpen_iInter_of_finite (fun i ↦ (isOpen_lt (continuous_const : Continuous (fun _ : Cover ↦ (0 : ℝ))) (PiLp.continuous_apply 2 _ i)).inter (isOpen_lt (PiLp.continuous_apply 2 _ i) (continuous_const : Continuous (fun _ : Cover ↦ (1 : ℝ)))))
  have hLU : L⊆U := by
    rintro y ⟨x,hx,rfl⟩ i
    simp only [PiLp.add_apply,PiLp.sub_apply]
    change 0<x i-c i+(1/2 : ℝ) ∧ x i-c i+1/2<1
    constructor <;> linarith [hbox x hx i]
  obtain ⟨φ,hφ,hφc,hφs,hφone⟩ := compact_smooth_cutoff hL hU hLU
  let f : Cover → Cover := fun y ↦ φ y • (y-cubeCenter)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hφ.smul (contDiff_id.sub contDiff_const)
  have hfc : HasCompactSupport f := hφc.smul_right
  have hfs : tsupport f⊆U := (tsupport_smul_subset_left φ (fun y ↦ y-cubeCenter)).trans hφs
  let X : Cover → Cover := fun x ↦ latticePeriodize f (x-c+cubeCenter)
  refine ⟨X,(latticePeriodize_contDiff hf hfc).comp ((contDiff_id.sub contDiff_const).add contDiff_const),?_,?_⟩
  · intro m x
    dsimp only [X]
    rw [show (x+latticeVector m)-c+cubeCenter=(x-c+cubeCenter)+latticeVector m by abel]
    exact latticePeriodize_periodic f m _
  · intro x hx
    have hxL : x-c+cubeCenter∈L := mem_image_of_mem _ hx
    have he := latticePeriodize_eventuallyEq hfc hfs (fun i ↦ ⟨(hLU hxL i).1.le,(hLU hxL i).2.le⟩)
    have hφx := hφone _ hxL
    have ht : Tendsto (fun y : Cover ↦ y-c+cubeCenter) (𝓝 x) (𝓝 (x-c+cubeCenter)) :=
      ((continuous_id.sub continuous_const).add continuous_const).continuousAt
    filter_upwards [he.comp_tendsto ht,ht hφx] with y hey hφy
    change latticePeriodize f (y-c+cubeCenter)=y-c
    change latticePeriodize f (y-c+cubeCenter)=f (y-c+cubeCenter) at hey
    rw [hey]
    dsimp only [f]
    rw [hφy,one_smul]
    abel

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def centeredLiftCell (c : Cover) : Set Cover := (fun y : Cover ↦ y+c-cubeCenter) '' closedFundamentalCube

lemma centeredLiftCell_compact (c : Cover) : IsCompact (centeredLiftCell c) :=
  isCompact_closedFundamentalCube.image ((continuous_id.add continuous_const).sub continuous_const)

lemma mem_centeredLiftCell {c x : Cover} : x∈centeredLiftCell c ↔
    ∀ i : Fin 3,c i-1/2≤x i ∧ x i≤c i+1/2 := by
  constructor
  · rintro ⟨y,⟨u,hu,rfl⟩,rfl⟩ i
    simp only [PiLp.sub_apply,PiLp.add_apply]
    change c i-1/2≤u i+c i-1/2 ∧ u i+c i-1/2≤c i+1/2
    have h0 : 0≤u i := hu.1 i
    have h1 : u i≤1 := hu.2 i
    constructor <;> linarith
  · intro hx
    refine ⟨x-c+cubeCenter,?_,by abel_nf⟩
    refine ⟨fun i ↦ x i-c i+1/2,⟨fun i ↦ ?_,fun i ↦ ?_⟩,?_⟩
    · change 0≤x i-c i+1/2
      linarith [(hx i).1]
    · change x i-c i+1/2≤1
      linarith [(hx i).2]
    · ext i; rfl

lemma exists_centeredLiftCell (c : Cover) (x : Cover) :
    ∃ y∈centeredLiftCell c,quotientMap y=quotientMap x := by
  let z := quotientMap (x-c+cubeCenter)
  refine ⟨representative z+c-cubeCenter,⟨representative z,representative_mem_closedCube z,rfl⟩,?_⟩
  rw [quotientMap_sub,quotientMap_add,quotientMap_representative]
  dsimp only [z]
  rw [quotientMap_add,quotientMap_sub]
  abel

theorem exists_boundary_periodic_position {O : Set Torus} (c : Cover)
    (hgap : ∀ x∈centeredLiftCell c,quotientMap x∈frontier O →
      ∀ i : Fin 3,c i-1/2<x i ∧ x i<c i+1/2) :
    ∃ X : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) X ∧
      (∀ m x,X (x+latticeVector m)=X x) ∧
      (∀ x∈centeredLiftCell c,quotientMap x∈frontier O →X x=x-c) ∧
      ∀ x : Cover,quotientMap x∈frontier O →fderiv ℝ X x=ContinuousLinearMap.id ℝ Cover := by
  let K := centeredLiftCell c∩quotientMap ⁻¹' frontier O
  have hK : IsCompact K := (centeredLiftCell_compact c).inter_right (isClosed_frontier.preimage continuous_quotientMap)
  obtain ⟨X,hX,hp,he⟩ := exists_periodic_position c hK (fun x hx ↦ hgap x hx.1 hx.2)
  refine ⟨X,hX,hp,fun x hx hb ↦ (he x ⟨hx,hb⟩).eq_of_nhds,?_⟩
  intro x hx
  obtain ⟨y,hy,hq⟩ := exists_centeredLiftCell c x
  have hyb : quotientMap y∈frontier O := by rwa [hq]
  have hdy := (he y ⟨hy,hyb⟩).fderiv_eq (𝕜 := ℝ)
  have hd : fderiv ℝ X y=ContinuousLinearMap.id ℝ Cover := by
    rw [hdy]
    simp only [fderiv_sub_const,fderiv_fun_id]
  obtain ⟨m,hm⟩ := same_quotient_lattice hq
  rwa [hm,fderiv_periodic hp] at hd

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma orientedUpperVertex_origin_apply (b : Fin 3 → Bool) (i : Fin 3) :
    orientedUpperVertex b (fun _ ↦ false) i=if b i then (1/2 : ℝ) else 1 := by
  cases h : b i <;> simp [orientedUpperVertex,upperVertex,h]

theorem isMinimizerAt_strict_support {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (b : Fin 3 → Bool)
    (hsg : ∀ i : Fin 3,∀ x : Cover,x i∈Ioo (1/2 : ℝ) 1 →
      quotientMap x∈frontier (openRepresentative E) →
      if b i then 0<N x i else N x i<0)
    {x : Cover} (hx : quotientMap x∈frontier (openRepresentative E))
    (hbox : ∀ i : Fin 3,orientedUpperVertex b (fun _ ↦ false) i-1/2<x i ∧
      x i<orientedUpperVertex b (fun _ ↦ false) i+1/2) :
    0<⟪N x,x-orientedUpperVertex b (fun _ ↦ false)⟫ := by
  classical
  let c := orientedUpperVertex b (fun _ ↦ false)
  have href (i : Fin 3) : (axisReflection i).torus (quotientMap x)∈frontier (openRepresentative E) := by
    have he := congrArg frontier (openRepresentative_congr_ae (hR i))
    rw [(axisReflection i).frontier_openRepresentative_preimage hE] at he
    change quotientMap x∈(axisReflection i).torus ⁻¹' frontier (openRepresentative E)
    rw [←he]
    exact hx
  have hpoint (i : Fin 3) : x i≠c i → 0<N x i*(x i-c i) := by
    intro hne
    have hc : c i=if b i then (1/2 : ℝ) else 1 := orientedUpperVertex_origin_apply b i
    have hbi := hbox i
    change c i-1/2<x i ∧ x i<c i+1/2 at hbi
    let r (k : ℤ) := (axisReflection i).cover x+latticeVector (Pi.single i k)
    have hrb (k : ℤ) : quotientMap (r k)∈frontier (openRepresentative E) := by
      simpa only [r,quotientMap_add,quotientMap_latticeVector,add_zero,(axisReflection i).commute] using href i
    have hrn (k : ℤ) : N (r k) i= -N x i := by
      rw [show r k=(axisReflection i).cover x+latticeVector (Pi.single i k) by rfl,hp,
        (axisReflection i).normal_equivariant hV hE hmin (hR i) hμ hN hp hae x hx]
      simp only [axisReflection_cover_apply,ite_true]
    have hrc (k : ℤ) : r k i= -x i+(k : ℝ) := by
      simp only [r,PiLp.add_apply,axisReflection_cover_apply,ite_true,latticeVector,Pi.single_eq_same]
    cases h : b i <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at hc
    · rcases lt_or_gt_of_ne hne with hlo|hhi
      · have hn := hsg i x ⟨by linarith [hbi.1],by linarith⟩ hx
        simp only [h,Bool.false_eq_true,ite_false] at hn
        exact mul_pos_of_neg_of_neg hn (sub_neg.mpr hlo)
      · have hn := hsg i (r 2) (by rw [hrc]; norm_num; constructor <;> linarith [hbi.2]) (hrb 2)
        simp only [h,Bool.false_eq_true,ite_false,hrn] at hn
        exact mul_pos (by linarith) (sub_pos.mpr hhi)
    · rcases lt_or_gt_of_ne hne with hlo|hhi
      · have hn := hsg i (r 1) (by rw [hrc]; norm_num; constructor <;> linarith [hbi.1]) (hrb 1)
        simp only [h,ite_true,hrn] at hn
        exact mul_pos_of_neg_of_neg (by linarith) (sub_neg.mpr hlo)
      · have hn := hsg i x ⟨by linarith,by linarith [hbi.2]⟩ hx
        simp only [h,ite_true] at hn
        exact mul_pos hn (sub_pos.mpr hhi)
  have hne : x≠c := by
    intro he
    apply isMinimizerAt_common_fixed_not_boundary hV hmin hR (quotientMap c) (upperVertex_fixed _)
    simpa only [he] using hx
  obtain ⟨i,hi⟩ : ∃ i : Fin 3,x i≠c i := by
    by_contra hn
    push Not at hn
    exact hne (by ext i; exact hn i)
  have hnon (j : Fin 3) : 0≤N x j*(x j-c j) := by
    by_cases he : x j=c j
    · rw [he,sub_self,mul_zero]
    · exact (hpoint j he).le
  have hh := Finset.single_le_sum (s := Finset.univ) (a := i) (fun j _ ↦ hnon j) (Finset.mem_univ i)
  have hpos := (hpoint i hi).trans_le hh
  simpa only [PiLp.inner_apply,PiLp.sub_apply,RCLike.inner_apply,RCLike.conj_to_real,
    mul_comm] using hpos

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circle_norm_half : ‖((1/2 : ℝ) : AddCircle (1 : ℝ))‖=(1/2 : ℝ) := by
  have hh := (AddCircle.norm_coe_eq_abs_iff 1 (x := 1/2) (by norm_num)).mpr (by norm_num)
  simpa using hh

lemma upperFold_cell_face (b : Fin 3 → Bool) (x : Cover) (i : Fin 3)
    (hf : x i=orientedUpperVertex b (fun _ ↦ false) i-1/2 ∨
      x i=orientedUpperVertex b (fun _ ↦ false) i+1/2) :
    upperFold (quotientMap x) i=if b i then (1 : ℝ) else 1/2 := by
  rw [orientedUpperVertex_origin_apply] at hf
  change 1-‖(x i : AddCircle (1 : ℝ))‖=if b i then (1 : ℝ) else 1/2
  cases h : b i <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at hf ⊢
  · rcases hf with hf|hf
    · norm_num at hf
      rw [hf,circle_norm_half]; ring
    · have he : x i=(1/2 : ℝ)+1 := by linarith
      rw [he,AddCircle.coe_add,AddCircle.coe_period,add_zero,circle_norm_half]; ring
  · rcases hf with hf|hf
    · norm_num at hf
      rw [hf,AddCircle.coe_zero,norm_zero,sub_zero]
    · have he : x i=1 := by linarith
      rw [he,AddCircle.coe_period,norm_zero,sub_zero]

theorem isMinimizerAt_one_vertex_gap {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 → Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (hv : ∀ i : Fin 3,quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    ∀ x∈centeredLiftCell (orientedUpperVertex b (fun _ ↦ false)),
      quotientMap x∈closure (openRepresentative E) →
      ∀ i : Fin 3,orientedUpperVertex b (fun _ ↦ false) i-1/2<x i ∧
        x i<orientedUpperVertex b (fun _ ↦ false) i+1/2 := by
  classical
  let c := orientedUpperVertex b (fun _ ↦ false)
  intro x hx hxb i
  have hbx := mem_centeredLiftCell.mp hx i
  change c i-1/2≤x i ∧ x i≤c i+1/2 at hbx
  have hn : x i≠c i-1/2 ∧ x i≠c i+1/2 := by
    apply not_or.mp
    intro hface
    let v := orientedUpperVertex b (fun j ↦ if j=i then true else false)
    have hf := upperFold_cell_face b x i hface
    have hord : OrientedCoordinateLE b v (upperFold (quotientMap x)) := by
      intro j
      by_cases hji : j=i
      · subst j
        dsimp only [v,orientedUpperVertex,upperVertex]
        simp only [ite_true,Bool.not_true]
        rw [hf]
        cases b i <;> simp
      · have hmin := orientedUpperVertex_min b (upperFold_mem (quotientMap x)) j
        have hvj : v j=c j := by
          dsimp [v,c,orientedUpperVertex,upperVertex]
          simp [hji]
        change (if b j then v j≤upperFold (quotientMap x) j else upperFold (quotientMap x) j≤v j)
        rw [hvj]
        exact hmin
    have hy : quotientMap (upperFold (quotientMap x))∈closure (openRepresentative E) := by
      have hc : Continuous (fun z : Torus ↦ quotientMap (upperFold z)) := continuous_quotientMap.comp upperFold_continuous
      apply (closure_minimal (s := openRepresentative E)
        (t := (fun z : Torus ↦ quotientMap (upperFold z)) ⁻¹' closure (openRepresentative E))
        (fun z hz ↦ subset_closure ((upperFold_phase (reflection_invariant_openRepresentative hmin.1.1 hR) z).mpr hz))
        (isClosed_closure.preimage hc)) hxb
    have hvc : quotientMap v∈closure (openRepresentative E) := octant_downset_closure
      (isOpen_openRepresentative E) (reflection_invariant_openRepresentative hmin.1.1 hR)
      hd (upperVertex_mem _) (upperFold_mem _) hord hy
    have hvb := isMinimizerAt_common_fixed_not_boundary hV hmin hR (quotientMap v) (upperVertex_fixed _)
    apply hvb
    rw [(isOpen_openRepresentative E).frontier_eq]
    exact ⟨hvc,hv i⟩
  exact ⟨lt_of_le_of_ne hbx.1 hn.1.symm,lt_of_le_of_ne hbx.2 hn.2⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma reflection_invariant_frontier {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈frontier (openRepresentative E) ↔
      z∈frontier (openRepresentative E) := by
  intro i z
  have hh := openRepresentative_congr_ae (hR i)
  rw [(axisReflection i).openRepresentative_preimage_null hE] at hh
  change z∈(axisReflection i).torus.toHomeomorph ⁻¹' frontier (openRepresentative E) ↔ _
  rw [(axisReflection i).torus.toHomeomorph.preimage_frontier]
  change z∈frontier ((axisReflection i).torus ⁻¹' openRepresentative E) ↔ _
  rw [←hh]

lemma isMinimizerAt_frontier_nonempty_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    (frontier (openRepresentative E)).Nonempty := by
  let : ConnectedSpace Torus := quotientMap_surjective.connectedSpace continuous_quotientMap
  by_contra hn
  have he := Set.not_nonempty_iff_eq_empty.mp hn
  rcases frontier_eq_empty_iff.mp he with h|h
  · exact (sibling_isMinimizerAt_openRepresentative_nonempty hV hmin).ne_empty h
  · have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
    obtain ⟨z,hz⟩ := sibling_isMinimizerAt_openRepresentative_nonempty hVc
      ((isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin)
    have hzO : z∈openRepresentative E := by rw [h]; trivial
    have hzcl := subset_closure hzO
    rw [isMinimizerAt_closure_openRepresentative_null hV hmin] at hzcl
    exact hz (by simpa only [compl_compl] using hzcl)

def axialSeamFunction (i : Fin 3) (x : Cover) : ℝ := Real.sin (2*Real.pi*x i)

lemma axialSeamFunction_continuous (i : Fin 3) : Continuous (axialSeamFunction i) := by
  exact Real.continuous_sin.comp ((continuous_const : Continuous (fun _ : Cover ↦ 2*Real.pi)).mul
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i))

lemma axialSeamFunction_periodic (i : Fin 3) :
    ∀ n x,axialSeamFunction i (x+latticeVector n)=axialSeamFunction i x := by
  intro n x
  unfold axialSeamFunction
  simp only [PiLp.add_apply,latticeVector]
  convert Real.sin_add_int_mul_two_pi (2*Real.pi*x i) (n i) using 1
  congr 1
  ring

lemma axialSeamFunction_reflection (i : Fin 3) (z : Torus) :
    axialSeamFunction i (representative ((axisReflection i).torus z))=
      -axialSeamFunction i (representative z) := by
  have he : (axisReflection i).torus z=quotientMap ((axisReflection i).cover (representative z)) := by
    rw [(axisReflection i).commute,quotientMap_representative]
  rw [he,periodic_representative (axialSeamFunction_periodic i)]
  simp only [axialSeamFunction,axisReflection_cover_apply,ite_true,mul_neg,Real.sin_neg]

lemma axialSeamFunction_zero_fold {i : Fin 3} {z : Torus}
    (h : axialSeamFunction i (representative z)=0) :
    upperFold z i=(1/2 : ℝ) ∨ upperFold z i=1 := by
  obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp h
  have he : (n : ℝ)=2*representative z i := by
    apply (mul_right_cancel₀ Real.pi_ne_zero)
    simpa only [axialSeamFunction] using hn.trans (by ring)
  have ht := representative_mem_fundamentalCube z i
  have hn0 : (0 : ℤ)≤n := by exact_mod_cast (show (0 : ℝ)≤(n : ℝ) by linarith [ht.1])
  have hn2 : n<(2 : ℤ) := by exact_mod_cast (show (n : ℝ)<(2 : ℝ) by linarith [ht.2])
  have hez : z i=((representative z i : ℝ) : AddCircle (1 : ℝ)) := by
    exact (congrArg (fun t : Torus ↦ t i) (quotientMap_representative z)).symm
  interval_cases n
  · right
    have hx : representative z i=0 := by norm_num at he; linarith
    change 1-‖z i‖=1
    rw [hez,hx,AddCircle.coe_zero,norm_zero,sub_zero]
  · left
    have hx : representative z i=(1/2 : ℝ) := by norm_num at he; linarith
    change 1-‖z i‖=1/2
    rw [hez,hx,circle_norm_half]; ring

theorem connected_reflected_boundary_meets_axial_seam {S : Set Torus}
    (hS : IsPreconnected S) (hne : S.Nonempty)
    (hR : ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈S ↔ z∈S)
    (i : Fin 3) : ∃ z∈S,upperFold z i=(1/2 : ℝ) ∨ upperFold z i=1 := by
  let f : Torus → ℝ := fun z ↦ axialSeamFunction i (representative z)
  have hf : Continuous f := continuous_periodic_descent (axialSeamFunction_continuous i)
    (axialSeamFunction_periodic i)
  obtain ⟨z,hz⟩ := hne
  have hr := (hR i z).mpr hz
  have he : f ((axisReflection i).torus z)= -f z := axialSeamFunction_reflection i z
  have hzero : ∃ y∈S,f y=0 := by
    rcases le_total (f z) 0 with h|h
    · obtain ⟨y,hy,hey⟩ := hS.intermediate_value hz hr hf.continuousOn
        (show (0 : ℝ)∈Icc (f z) (f ((axisReflection i).torus z)) by rw [he]; exact ⟨h,by linarith⟩)
      exact ⟨y,hy,hey⟩
    · obtain ⟨y,hy,hey⟩ := hS.intermediate_value hr hz hf.continuousOn
        (show (0 : ℝ)∈Icc (f ((axisReflection i).torus z)) (f z) by rw [he]; exact ⟨by linarith,h⟩)
      exact ⟨y,hy,hey⟩
  obtain ⟨y,hy,hey⟩ := hzero
  exact ⟨y,hy,axialSeamFunction_zero_fold hey⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axisFixedHeights : Set AxisCircle := {0,((1/2 : ℝ) : AxisCircle)}

lemma axisFixedHeights_finite : axisFixedHeights.Finite := (Set.finite_singleton _).insert _
lemma axisCircle_singleton_null (x : AxisCircle) : volume ({x} : Set AxisCircle)=0 := by
  let : Fact (0<(1 : ℝ)) := ⟨by norm_num⟩
  have hh := AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) (ε := (0 : ℝ))
  simpa using hh

end CubicTorus
end
end
end

end OAI
