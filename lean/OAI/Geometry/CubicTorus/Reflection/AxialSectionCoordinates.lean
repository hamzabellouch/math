import Mathlib
import OAI.Geometry.CubicTorus.Reflection.AxialWeightedHeight

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSplit (i : Fin 3) : Cover ≃ᵐ ℝ × Plane :=
  (coverCoordinatePermute (Equiv.swap 0 i)).toMeasurableEquiv.trans UpperComparison.tubeSplit

lemma axialSplit_measurePreserving (i : Fin 3) : MeasurePreserving (axialSplit i) :=
  UpperComparison.tubeSplit_measurePreserving.comp (coverCoordinatePermute (Equiv.swap 0 i)).measurePreserving

@[simp] lemma axialSplit_fst (i : Fin 3) (x : Cover) : (axialSplit i x).1=x i := by
  simp [axialSplit]

@[simp] lemma axialSplit_symm_axis (i : Fin 3) (z : ℝ × Plane) : (axialSplit i).symm z i=z.1 := by
  simpa only [axialSplit_fst] using congrArg Prod.fst ((axialSplit i).apply_symm_apply z)

lemma continuous_axialSplit (i : Fin 3) : Continuous (axialSplit i) :=
  UpperComparison.continuous_tubeSplit.comp (coverCoordinatePermute (Equiv.swap 0 i)).continuous

lemma continuous_axialSplit_symm (i : Fin 3) : Continuous (axialSplit i).symm :=
  (coverCoordinatePermute (Equiv.swap 0 i)).symm.continuous.comp UpperComparison.continuous_tubeSplit_symm

def transverseSquare : Set Plane := {y | ∀ j,0≤y j ∧ y j<1}

lemma measurableSet_transverseSquare : MeasurableSet transverseSquare := by
  change MeasurableSet {y : Plane | ∀ j,y j∈Ico (0 : ℝ) 1}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun j =>
    measurableSet_Ico.preimage (EuclideanSpace.proj j : Plane →L[ℝ] ℝ).measurable)

lemma transverseSquare_subset_ball : transverseSquare⊆Metric.closedBall (0 : Plane) 2 := by
  intro y hy
  rw [Metric.mem_closedBall,dist_zero_right]
  have hh : ‖y‖^2≤2 := by
    rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two]
    have h0 := hy 0
    have h1 := hy 1
    simp only [Real.norm_eq_abs,sq_abs]
    nlinarith [sq_nonneg (y 0),sq_nonneg (y 1)]
  nlinarith [norm_nonneg y]

lemma volume_transverseSquare_lt_top : volume transverseSquare<⊤ :=
  (measure_mono transverseSquare_subset_ball).trans_lt measure_closedBall_lt_top

lemma mem_axialSplit_cube (i : Fin 3) (x : Cover) :
    x∈fundamentalCube ↔ axialSplit i x∈Ico (0 : ℝ) 1 ×ˢ transverseSquare := by
  let y := coverCoordinatePermute (Equiv.swap 0 i) x
  have he : x∈fundamentalCube ↔ y∈fundamentalCube := by
    constructor
    · intro hx j
      exact hx ((Equiv.swap 0 i) j)
    · intro hy j
      have hh := hy ((Equiv.swap 0 i) j)
      simpa [y] using hh
  rw [he]
  change (∀ j,0≤y j ∧ y j<1) ↔ (0≤y 0 ∧ y 0<1) ∧ ∀ j : Fin 2,0≤y j.succ ∧ y j.succ<1
  constructor
  · intro hy
    exact ⟨hy 0,fun j => hy j.succ⟩
  · rintro ⟨h0,hs⟩ j
    exact Fin.cases h0 hs j

lemma axialSplit_preimage_cube (i : Fin 3) :
    axialSplit i ⁻¹' (Ico (0 : ℝ) 1 ×ˢ transverseSquare)=fundamentalCube := by
  ext x
  exact (mem_axialSplit_cube i x).symm

def axialSection (E : Set Torus) (i : Fin 3) (t : ℝ) : Set Plane :=
  transverseSquare∩(fun y => quotientMap ((axialSplit i).symm (t,y))) ⁻¹' E

def axialSectionArea (E : Set Torus) (i : Fin 3) (t : ℝ) : ℝ :=
  volume.real (axialSection E i t)

lemma measurableSet_axialSection {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) (t : ℝ) :
    MeasurableSet (axialSection E i t) :=
  measurableSet_transverseSquare.inter (hE.preimage
    (measurable_quotientMap.comp ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id))))

lemma volume_axialSection_lt_top (E : Set Torus) (i : Fin 3) (t : ℝ) :
    volume (axialSection E i t)<⊤ :=
  (measure_mono inter_subset_left).trans_lt volume_transverseSquare_lt_top

lemma axialSectionArea_nonneg (E : Set Torus) (i : Fin 3) (t : ℝ) :
    0≤axialSectionArea E i t := ENNReal.toReal_nonneg

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volume_axialSquare : volume transverseSquare=1 := by
  have he := (axialSplit_measurePreserving 0).measure_preimage
    ((measurableSet_Ico (a := (0 : ℝ)) (b := 1)).prod measurableSet_transverseSquare).nullMeasurableSet
  rw [axialSplit_preimage_cube,volume_fundamentalCube,Measure.volume_eq_prod,
    Measure.prod_prod,Real.volume_Ico] at he
  simpa using he.symm

lemma volume_axialRectangle : volume (Ico (0 : ℝ) 1 ×ˢ transverseSquare)=1 := by
  rw [Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Ico,volume_axialSquare]
  norm_num

lemma axialSectionArea_le_one (E : Set Torus) (i : Fin 3) (t : ℝ) :
    axialSectionArea E i t≤1 := by
  have he : volume (axialSection E i t)≤1 := (measure_mono inter_subset_left).trans_eq volume_axialSquare
  exact (ENNReal.toReal_mono (by simp) he).trans_eq (by simp)

lemma axial_section_inner {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) (t c : ℝ) :
    (∫ y in transverseSquare,characteristic E (quotientMap ((axialSplit i).symm (t,y)))*c)=
      axialSectionArea E i t*c := by
  let B : Set Plane := (fun y => quotientMap ((axialSplit i).symm (t,y))) ⁻¹' E
  have hB : MeasurableSet B := hE.preimage
    (measurable_quotientMap.comp ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  have he : (fun y => characteristic E (quotientMap ((axialSplit i).symm (t,y)))*c)=
      B.indicator (fun _ => c) := by
    funext y
    by_cases hy : y∈B
    · simp only [indicator_of_mem hy]
      change quotientMap ((axialSplit i).symm (t,y))∈E at hy
      simp only [characteristic,indicator_of_mem hy,one_mul]
    · simp only [indicator_of_notMem hy]
      change quotientMap ((axialSplit i).symm (t,y))∉E at hy
      simp only [characteristic,indicator_of_notMem hy,zero_mul]
  rw [he,setIntegral_indicator hB,integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
  rfl

lemma integrable_axialIndicator {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    IntegrableOn (fun z : ℝ × Plane => characteristic E (quotientMap ((axialSplit i).symm z))*f z.1)
      (Ico (0 : ℝ) 1 ×ˢ transverseSquare) := by
  obtain ⟨M,hM0,hM⟩ := periodic_bounded
    (hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous) (axial_function_periodic i hp)
  apply IntegrableOn.of_bound (by rw [volume_axialRectangle]; simp)
    (((measurable_characteristic hE).comp (measurable_quotientMap.comp (axialSplit i).symm.measurable)).mul
      (hf.measurable.comp measurable_fst)).aestronglyMeasurable M
  apply Eventually.of_forall
  intro z
  have hb : ‖f z.1‖≤M := by
    have hh := hM ((axialSplit i).symm z)
    change ‖f ((axialSplit i).symm z i)‖≤M at hh
    simpa only [axialSplit_symm_axis] using hh
  change ‖characteristic E (quotientMap ((axialSplit i).symm z))*f z.1‖≤M
  by_cases hz : quotientMap ((axialSplit i).symm z)∈E
  · simpa only [characteristic,indicator_of_mem hz,one_mul] using hb
  · simp only [characteristic,indicator_of_notMem hz,zero_mul,norm_zero]
    exact hM0

theorem axial_section_fubini {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))=
      ∫ t in Ico (0 : ℝ) 1,axialSectionArea E i t*f t := by
  let g : ℝ × Plane → ℝ := fun z => characteristic E (quotientMap ((axialSplit i).symm z))*f z.1
  have he := (axialSplit_measurePreserving i).setIntegral_preimage_emb
    (axialSplit i).measurableEmbedding g (Ico (0 : ℝ) 1 ×ˢ transverseSquare)
  rw [axialSplit_preimage_cube] at he
  have hleft : (fun x : Cover => g (axialSplit i x))=
      (quotientMap ⁻¹' E).indicator (fun x => f (x i)) := by
    funext x
    dsimp [g]
    rw [(axialSplit i).symm_apply_apply,axialSplit_fst]
    by_cases hx : quotientMap x∈E <;> simp [characteristic,hx]
  rw [hleft,setIntegral_indicator (hE.preimage measurable_quotientMap)] at he
  rw [he]
  have hi := integrable_axialIndicator hE i hf hp
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod _ hi]
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  exact axial_section_inner hE i t (f t)

lemma integrable_axialSectionArea {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    IntegrableOn (axialSectionArea E i) (Ico (0 : ℝ) 1) := by
  have hi := integrable_axialIndicator hE i (f := fun _ => 1) continuous_const (fun _ => rfl)
  rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict] at hi
  have hh := hi.integral_prod_left
  change Integrable (axialSectionArea E i) (volume.restrict (Ico (0 : ℝ) 1))
  convert hh using 1
  funext t
  simpa only [mul_one] using (axial_section_inner hE i t 1).symm

lemma integral_axialSectionArea {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    (∫ t in Ico (0 : ℝ) 1,axialSectionArea E i t)=torusVolume.real E := by
  have he := axial_section_fubini hE i (f := fun _ => 1) continuous_const (fun _ => rfl)
  rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one,← realVolume_lift hE] at he
  simpa only [mul_one] using he.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodic_deriv {f : ℝ → ℝ} (hp : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro x
  have he : (fun t => f (t+1))=f := funext hp
  simpa only [deriv_comp_add_const] using congrArg (fun g => deriv g x) he

lemma axial_section_periodic_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    (∫ t in (0 : ℝ)..1,axialSectionArea E i t*deriv f t)=
      ∫ z,((z.2 : Cover) i)*f (z.1.1 i) ∂(μ : Measure NormalBundle) := by
  let F : Cover → Cover := fun x => f (x i) • EuclideanSpace.single i 1
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).smul contDiff_const
  have hpF : ∀ m x,F (x+latticeVector m)=F x := by
    intro m x
    exact congrArg (fun t : ℝ => t • (EuclideanSpace.single i 1 : Cover))
      (axial_function_periodic i hp m x)
  have he := periodic_normal_flux hμ hF hpF
  simp only [F,divergence_axial i (hf.differentiable (by simp))] at he
  have hn (z : NormalBundle) : ⟪(z.2 : Cover),f (z.1.1 i) • EuclideanSpace.single i 1⟫=
      ((z.2 : Cover) i)*f (z.1.1 i) := by
    simp [PiLp.inner_apply,EuclideanSpace.single,mul_comm]
  simp_rw [hn] at he
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),
    ← integral_Ico_eq_integral_Ioc,
    ← axial_section_fubini hE i (hf.continuous_deriv (by simp)) (periodic_deriv hp)]
  exact he.symm

theorem axial_section_integrable_weak_derivative {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (hac : Measure.map (axialBundleHeight i) (μ : Measure NormalBundle)≪volume) :
    ∃ v : ℝ → ℝ,IntegrableOn v (Icc (0 : ℝ) 1) ∧
      ∀ ψ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ⊆Ioo (0 : ℝ) 1 →
      (∫ t,axialSectionArea E i t*deriv ψ t)=-(∫ t,v t*ψ t) := by
  have hw : Continuous (fun z : NormalBundle => -((z.2 : Cover) i)) :=
    ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp continuous_normalUnit).neg
  obtain ⟨g,hg,hgm⟩ := circle_weighted_density (μ : Measure NormalBundle)
    (continuous_axialBundleHeight i) hac hw
  refine ⟨fun t => g (t : AddCircle (1 : ℝ)),?_,?_⟩
  · simpa only [zero_add] using circle_integrable_preimage_Icc hg 0
  intro ψ hψ hs
  have hc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset isClosed_closure
    (hs.trans Ioo_subset_Icc_self)
  let f := circlePeriodize ψ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := circlePeriodize_contDiff hψ hc
  have hp : Function.Periodic f 1 := circlePeriodize_periodic ψ
  have heval (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : f t=ψ t :=
    (circlePeriodize_unit_eventuallyEq hc hs ht).eq_of_nhds
  have hder (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : deriv f t=deriv ψ t :=
    (circlePeriodize_unit_eventuallyEq hc hs ht).deriv_eq
  have hflux := axial_section_periodic_flux hE hμ i hf hp
  have hl : (∫ t in (0 : ℝ)..1,axialSectionArea E i t*deriv f t)=
      ∫ t,axialSectionArea E i t*deriv ψ t := by
    calc
      _=∫ t in (0 : ℝ)..1,axialSectionArea E i t*deriv ψ t := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hder t (by simpa [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using ht)]
      _=_ := integral_compact_eq_interval (by norm_num)
        ((tsupport_deriv_subset (f := ψ)).trans hs)
  rw [hl] at hflux
  have hdens := hgm hp.lift (continuous_periodic_lift hp hf.continuous)
  have hdc : (∫ t : AddCircle (1 : ℝ),g t*hp.lift t)=
      ∫ t : ℝ,g (t : AddCircle (1 : ℝ))*ψ t := by
    rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0]
    simp only [zero_add,Function.Periodic.lift_coe]
    calc
      _=∫ t in (0 : ℝ)..1,g (t : AddCircle (1 : ℝ))*ψ t := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [heval t (by simpa [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using ht)]
      _=_ := integral_compact_eq_interval (by norm_num) hs
  rw [hdc] at hdens
  have hn : (∫ z,-((z.2 : Cover) i)*hp.lift (axialBundleHeight i z) ∂(μ : Measure NormalBundle))=
      -(∫ z,((z.2 : Cover) i)*f (z.1.1 i) ∂(μ : Measure NormalBundle)) := by
    simp only [axialBundleHeight,Function.Periodic.lift_coe,neg_mul,integral_neg]
  rw [hn] at hdens
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSplit_symm_transverse_line (i : Fin 3) (t u w : ℝ) :
    (axialSplit i).symm (t,planeFaceCoordinates.symm (u,w))=
      (axialSplit i).symm (t,planeFaceCoordinates.symm (u,0))+
        w • EuclideanSpace.single ((Equiv.swap 0 i) 2) 1 := by
  let L := coverCoordinatePermute (Equiv.swap 0 i)
  change L.symm (UpperComparison.tubeSplit.symm _) = L.symm (UpperComparison.tubeSplit.symm _)+_
  apply L.injective
  rw [map_add,map_smul,L.apply_symm_apply,L.apply_symm_apply]
  change UpperComparison.tubeSplit.symm _=UpperComparison.tubeSplit.symm _+
    w • coverCoordinatePermute (Equiv.swap 0 i) (EuclideanSpace.single ((Equiv.swap 0 i) 2) 1)
  rw [coverCoordinatePermute_single,Equiv.symm_apply_apply]
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,UpperComparison.tubeSplit_symm_succ]
    fin_cases j
    · change u=u+w*0
      ring
    · change w=0+w*1
      ring

theorem isMinimizerAt_axial_boundary_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) (t : ℝ) :
    volume {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier (openRepresentative E)}=0 := by
  let S : Set (ℝ × ℝ) := {z | quotientMap ((axialSplit i).symm (t,planeFaceCoordinates.symm z))∈
    frontier (openRepresentative E)}
  have hS : MeasurableSet S := isClosed_frontier.measurableSet.preimage
    (measurable_quotientMap.comp ((axialSplit i).symm.measurable.comp
      (measurable_const.prodMk planeFaceCoordinates.symm.continuous.measurable)))
  have hz : (volume.prod volume) S=0 := by
    apply Measure.measure_prod_null_of_ae_null hS
    apply Eventually.of_forall
    intro u
    have he : Prod.mk u ⁻¹' S={w : ℝ | quotientMap
      ((axialSplit i).symm (t,planeFaceCoordinates.symm (u,0))+
        w • EuclideanSpace.single ((Equiv.swap 0 i) 2) 1)∈frontier (openRepresentative E)} := by
      ext w
      change (quotientMap ((axialSplit i).symm (t,planeFaceCoordinates.symm (u,w)))∈frontier (openRepresentative E)) ↔ _
      rw [axialSplit_symm_transverse_line]
      rfl
    change volume (Prod.mk u ⁻¹' S)=0
    rw [he]
    exact (isMinimizerAt_countable_axial_boundary hV hE hm hμ hN hp ha hs hsg _ _).measure_zero volume
  have he := planeFaceCoordinates_measurePreserving.measure_preimage hS.nullMeasurableSet
  have hid : planeFaceCoordinates ⁻¹' S=
      {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier (openRepresentative E)} := by
    ext y
    simp [S]
  rw [hid,Measure.volume_eq_prod,hz] at he
  exact he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_axialSectionArea_of_boundary_null {F : Set Torus}
    (hF : MeasurableSet F) (i : Fin 3)
    (hz : ∀ t : ℝ,volume {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier F}=0) :
    Continuous (axialSectionArea F i) := by
  have hid : axialSectionArea F i=(fun t => ∫ y in transverseSquare,
      characteristic F (quotientMap ((axialSplit i).symm (t,y)))) := by
    funext t
    simpa only [mul_one] using (axial_section_inner hF i t 1).symm
  rw [hid,continuous_iff_continuousAt]
  intro t
  apply continuousAt_of_dominated (bound := fun _ : Plane => (1 : ℝ))
  · apply Eventually.of_forall
    intro u
    exact ((measurable_characteristic hF).comp (measurable_quotientMap.comp
      ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
  · exact Eventually.of_forall fun _ => Eventually.of_forall fun y =>
      characteristic_bound F _
  · exact integrableOn_const volume_transverseSquare_lt_top.ne
  · have hnull : ∀ᵐ y : Plane,quotientMap ((axialSplit i).symm (t,y))∉frontier F := by
      rw [ae_iff]
      simpa only [not_not] using hz t
    filter_upwards [ae_restrict_of_ae hnull] with y hy
    have hc : ContinuousAt (characteristic F) (quotientMap ((axialSplit i).symm (t,y))) :=
      (continuousOn_const : ContinuousOn (fun _ : Torus => (1 : ℝ)) (interior F)).continuousAt_indicator hy
    have hg : ContinuousAt (fun u : ℝ => quotientMap ((axialSplit i).symm (u,y))) t :=
      (continuous_quotientMap.comp ((continuous_axialSplit_symm i).comp
        (continuous_id.prodMk continuous_const))).continuousAt
    exact ContinuousAt.comp (f := fun u : ℝ => quotientMap ((axialSplit i).symm (u,y))) hc hg

theorem isMinimizerAt_continuous_axial_sections {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) : Continuous (axialSectionArea (openRepresentative E) i) :=
  continuous_axialSectionArea_of_boundary_null (isOpen_openRepresentative E).measurableSet i
    (isMinimizerAt_axial_boundary_null hV hE hm hμ hN hp ha hs hsg i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma mem_coordinateHalf_of_interval (s : Fin 3 → Bool) (i : Fin 3) {x : Cover}
    (hx : x i∈Ioo (chamberCorner s i) (chamberCorner s i+1/2)) :
    quotientMap x∈coordinateHalf i (if s i then 0 else 1/2) := by
  rw [mem_coordinateHalf_quotient]
  cases hs : s i
  · simp only [chamberCorner,hs,Bool.false_eq_true,ite_false,zero_add] at hx
    simp only [Bool.false_eq_true,ite_false]
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · nlinarith [Real.pi_pos,hx.2]
    · nlinarith [Real.pi_pos,hx.1]
  · simp only [chamberCorner,hs,ite_true] at hx
    simp only [ite_true,sub_zero]
    have hr := Real.sin_neg_of_neg_of_neg_pi_lt
      (show 2*Real.pi*x i-2*Real.pi<0 by nlinarith [Real.pi_pos,hx.2])
      (show -Real.pi<2*Real.pi*x i-2*Real.pi by nlinarith [Real.pi_pos,hx.1])
    simpa only [Real.sin_sub_two_pi] using hr

lemma axialSplit_symm_axis_line (i : Fin 3) (u v : ℝ) (y : Plane) :
    (axialSplit i).symm (u,y)=(axialSplit i).symm (v,y)+(u-v) • EuclideanSpace.single i 1 := by
  let L := coverCoordinatePermute (Equiv.swap 0 i)
  change L.symm (UpperComparison.tubeSplit.symm _) = L.symm (UpperComparison.tubeSplit.symm _)+_
  apply L.injective
  rw [map_add,map_smul,L.apply_symm_apply,L.apply_symm_apply]
  change UpperComparison.tubeSplit.symm _=UpperComparison.tubeSplit.symm _+
    (u-v) • coverCoordinatePermute (Equiv.swap 0 i) (EuclideanSpace.single i 1)
  rw [coverCoordinatePermute_single]
  simp only [Equiv.symm_swap,Equiv.swap_apply_right]
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp

theorem isMinimizerAt_axialSection_nested {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) {u v : ℝ}
    (hu : u∈Ioo (chamberCorner s i) (chamberCorner s i+1/2))
    (hv : v∈Ioo (chamberCorner s i) (chamberCorner s i+1/2)) (huv : u≤v) :
    axialSection (openRepresentative E) i v⊆axialSection (openRepresentative E) i u := by
  rintro y ⟨hy,hyE⟩
  refine ⟨hy,?_⟩
  let a : Cover := (v-u) • EuclideanSpace.single i 1
  have hU : IsOpen (coordinateHalf i (if s i then 0 else 1/2)) := by
    cases hs : s i
    · simp only [Bool.false_eq_true,ite_false]
      rw [← coordinateReflection_preimage_half]
      exact (coordinateHalf_open i).preimage (coordinateReflection_continuous i)
    · simpa only [ite_true] using coordinateHalf_open i
  have hpos : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩
      coordinateHalf i (if s i then 0 else 1/2) → 0≤⟪N x,a⟫ := by
    intro x hx
    simp only [a,inner_smul_right,EuclideanSpace.inner_single_right,one_mul]
    exact mul_nonneg (sub_nonneg.mpr huv) (hsg x i hx).le
  have hpath : ∀ t∈Icc (0 : ℝ) 1,
      quotientMap ((axialSplit i).symm (v,y))-quotientMap (t • a)∈
        coordinateHalf i (if s i then 0 else 1/2) := by
    intro t ht
    rw [← quotientMap_sub]
    apply mem_coordinateHalf_of_interval
    simp only [PiLp.sub_apply,PiLp.smul_apply,a,PiLp.single_apply,ite_true,smul_eq_mul,mul_one,
      axialSplit_symm_axis]
    constructor <;> nlinarith [hu.1,hu.2,hv.1,hv.2,
      mul_nonneg ht.1 (sub_nonneg.mpr huv),mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr huv)]
  have hh := isMinimizerAt_monotone_segment hV hE hm hμ ha hU hpos hyE hpath
  rw [← quotientMap_sub] at hh
  have he : (axialSplit i).symm (v,y)-a=(axialSplit i).symm (u,y) := by
    rw [axialSplit_symm_axis_line i v u y]
    change (axialSplit i).symm (u,y)+a-a=_
    exact add_sub_cancel_right _ _
  rwa [he] at hh

lemma isMinimizerAt_antitoneOn_axialSectionArea_open {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) : AntitoneOn (axialSectionArea (openRepresentative E) i)
      (Ioo (chamberCorner s i) (chamberCorner s i+1/2)) := by
  intro u hu v hv huv
  exact ENNReal.toReal_mono (volume_axialSection_lt_top _ i u).ne
    (measure_mono (isMinimizerAt_axialSection_nested hV hE hm hμ ha hsg i hu hv huv))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma antitoneOn_closed_of_open {f : ℝ → ℝ} {a b : ℝ} (hab : a<b)
    (hf : Continuous f) (hm : AntitoneOn f (Ioo a b)) : AntitoneOn f (Icc a b) := by
  intro u hu v hv huv
  let c := (a+b)/2
  let F := fun (x t : ℝ) => (1-t)*x+t*c
  have hc : c∈Ioo a b := ⟨by dsimp [c]; linarith,by dsimp [c]; linarith⟩
  have hF : ∀ x∈Icc a b,∀ t∈Ioo (0 : ℝ) 1,F x t∈Ioo a b := by
    intro x hx t ht
    dsimp [F]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr hx.1),
        mul_pos ht.1 (sub_pos.mpr hc.1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr hx.2),
        mul_pos ht.1 (sub_pos.mpr hc.2)]
  have hlim : ∀ x : ℝ,Tendsto (fun t => f (F x t)) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
    intro x
    have he : F x 0=x := by simp [F]
    simpa only [Function.comp_def,he] using
      ((hf.comp (by fun_prop : Continuous (F x))).continuousAt (x := 0)).tendsto.mono_left
        (show 𝓝[>] (0 : ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto (hlim v) (hlim u)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ),t<1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [self_mem_nhdsWithin,hsmall] with t ht ht1
  apply hm (hF u hu t ⟨ht,ht1⟩) (hF v hv t ⟨ht,ht1⟩)
  dsimp [F]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr huv)]

theorem isMinimizerAt_antitoneOn_axialSectionArea {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) : AntitoneOn (axialSectionArea (openRepresentative E) i)
      (Icc (chamberCorner s i) (chamberCorner s i+1/2)) :=
  antitoneOn_closed_of_open (by linarith)
    (isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i)
    (isMinimizerAt_antitoneOn_axialSectionArea_open hV hE hm hμ ha hsg i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_absolutelyContinuous_axialSectionArea {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    AbsolutelyContinuousOnInterval (axialSectionArea (openRepresentative E) i) 0 1 := by
  have hμ' : IsNormalMeasure (openRepresentative E) μ :=
    hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hm).symm
  obtain ⟨v,hv,hw⟩ := axial_section_integrable_weak_derivative
    (isOpen_openRepresentative E).measurableSet hμ' i
    (isMinimizerAt_axialHeight_absolutelyContinuous hV hE hm hμ hN hp ha hs hsg hH i)
  exact absolutelyContinuous_of_integrable_weak_derivative
    (isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i)
    (by norm_num) hv hw

lemma chamber_interval_subset_unit (s : Fin 3 → Bool) (i : Fin 3) :
    uIcc (chamberCorner s i) (chamberCorner s i+1/2)⊆uIcc (0 : ℝ) 1 := by
  intro t ht
  rw [uIcc_of_le (by linarith)] at ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
  cases h : s i <;> simp only [chamberCorner,h,Bool.false_eq_true,ite_false,ite_true]
    at ht <;> constructor <;> linarith [ht.1,ht.2]

theorem isMinimizerAt_axialSection_fundamentalTheorem {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    (∫ t in chamberCorner s i..chamberCorner s i+1/2,
      deriv (axialSectionArea (openRepresentative E) i) t)=
      axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2)-
      axialSectionArea (openRepresentative E) i (chamberCorner s i) :=
  ((isMinimizerAt_absolutelyContinuous_axialSectionArea hV hE hm hμ hN hp ha hs hsg hH i).mono
    (chamber_interval_subset_unit s i)).integral_deriv_eq_sub

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Classical
namespace CubicTorus

lemma periodic_unit_sine : Function.Periodic (fun t : ℝ => Real.sin (2*Real.pi*t)) 1 := by
  intro t
  dsimp only
  rw [show 2*Real.pi*(t+1)=2*Real.pi*t+2*Real.pi by ring,Real.sin_add_two_pi]

def circleUnitSine : AddCircle (1 : ℝ) → ℝ := periodic_unit_sine.lift

lemma continuous_circleUnitSine : Continuous circleUnitSine :=
  continuous_periodic_lift periodic_unit_sine (Real.continuous_sin.comp (continuous_const.mul continuous_id))

@[simp] lemma circleUnitSine_coe (t : ℝ) : circleUnitSine t=Real.sin (2*Real.pi*t) :=
  Function.Periodic.lift_coe periodic_unit_sine t

def chamberHeightSign (b : Bool) (t : AddCircle (1 : ℝ)) : ℝ :=
  if (if b then circleUnitSine t<0 else 0<circleUnitSine t) then 1 else -1

lemma measurable_chamberHeightSign (b : Bool) : Measurable (chamberHeightSign b) := by
  unfold chamberHeightSign
  apply Measurable.ite _ measurable_const measurable_const
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact measurableSet_lt measurable_const continuous_circleUnitSine.measurable
  · exact measurableSet_lt continuous_circleUnitSine.measurable measurable_const

lemma norm_chamberHeightSign (b : Bool) (t : AddCircle (1 : ℝ)) : ‖chamberHeightSign b t‖=1 := by
  unfold chamberHeightSign
  split_ifs <;> norm_num

lemma chamberHeightSign_left (b : Bool) {t : ℝ} (ht : t∈Ioo (0 : ℝ) (1/2)) :
    chamberHeightSign b t=(if b then -1 else 1) := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi (show 0<2*Real.pi*t from mul_pos (by positivity) ht.1)
    (show 2*Real.pi*t<Real.pi by nlinarith [Real.pi_pos,ht.2])
  cases b <;> simp [chamberHeightSign,hsin,not_lt.mpr hsin.le]

lemma chamberHeightSign_right (b : Bool) {t : ℝ} (ht : t∈Ioo (1/2 : ℝ) 1) :
    chamberHeightSign b t=(if b then 1 else -1) := by
  have hs := Real.sin_neg_of_neg_of_neg_pi_lt
    (show 2*Real.pi*t-2*Real.pi<0 by nlinarith [Real.pi_pos,ht.2])
    (show -Real.pi<2*Real.pi*t-2*Real.pi by nlinarith [Real.pi_pos,ht.1])
  rw [Real.sin_sub_two_pi] at hs
  cases b <;> simp [chamberHeightSign,hs,not_lt.mpr hs.le]

lemma chamberHeightSign_eq_half (s : Fin 3 → Bool) (i : Fin 3) (x : Cover) :
    chamberHeightSign (s i) (x i)=
      if quotientMap x∈coordinateHalf i (if s i then 0 else 1/2) then 1 else -1 := by
  rw [mem_coordinateHalf_quotient]
  cases h : s i
  · simp only [Bool.false_eq_true,ite_false,chamberHeightSign,circleUnitSine_coe]
    rw [show 2*Real.pi*(x i-1/2)=2*Real.pi*x i-Real.pi by ring,Real.sin_sub_pi]
    simp
  · simp [chamberHeightSign,circleUnitSine_coe]

theorem isMinimizerAt_normal_chamberHeightSign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {x : Cover} (hx : quotientMap x∈frontier (openRepresentative E)) (i : Fin 3) :
    N x i*chamberHeightSign (s i) (x i)=|N x i| := by
  by_cases hz : coordinateSine i x=0
  · have hz' : coordinateSine i (representative (quotientMap x))=0 := by
      rwa [periodic_representative (coordinateSine_periodic i)]
    have hn := isMinimizerAt_normal_coordinate_seam_zero hV hE hm hμ hN hp ha i (hs i) hx hz'
    rw [periodic_representative hp] at hn
    simp [hn]
  have hz' : coordinateSine i (representative (quotientMap x))≠0 := by
    rwa [periodic_representative (coordinateSine_periodic i)]
  rw [chamberHeightSign_eq_half]
  obtain hh|hh := coordinateHalf_pair s (quotientMap x) i hz'
  · rw [ite_eq_left hh,mul_one,abs_of_pos (hsg x i ⟨hx,hh⟩)]
  · have hry : quotientMap (coverCoordinateReflection i x)∈frontier (openRepresentative E) := by
      rw [quotientMap_coordinateReflection]
      change quotientMap x∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
      rwa [frontier_reflection_invariant hE i (hs i)]
    have hn := hsg (coverCoordinateReflection i x) i
      ⟨hry,by rwa [quotientMap_coordinateReflection]⟩
    have he := congrArg (fun v : Cover => v i)
      (isMinimizerAt_normal_reflection hV hE hm hμ hN hp ha i (hs i) x hx)
    simp only [coverCoordinateReflection_apply,ite_true] at he
    have hnx : N x i<0 := by rw [he]; linarith
    have hno : quotientMap x∉coordinateHalf i (if s i then 0 else 1/2) := by
      intro hh; exact (hsg x i ⟨hx,hh⟩).not_gt hnx
    rw [ite_eq_right hno,mul_neg_one,abs_of_neg hnx]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSection_periodic (E : Set Torus) (i : Fin 3) :
    Function.Periodic (axialSection E i) 1 := by
  intro t
  ext y
  have he : EuclideanSpace.single i (1 : ℝ)=latticeVector (Pi.single i (1 : ℤ)) := by
    ext j
    simp [latticeVector,Pi.single_apply]
  have hq : quotientMap ((axialSplit i).symm (t+1,y))=quotientMap ((axialSplit i).symm (t,y)) := by
    rw [axialSplit_symm_axis_line i (t+1) t y,show t+1-t=1 by ring,one_smul,he,
      quotientMap_add,quotientMap_latticeVector,add_zero]
  simp only [axialSection,mem_inter_iff,mem_preimage,hq]

lemma axialSectionArea_periodic (E : Set Torus) (i : Fin 3) :
    Function.Periodic (axialSectionArea E i) 1 := fun t =>
  congrArg (fun S : Set Plane => volume.real S) (axialSection_periodic E i t)

lemma chamberSign_integral_deriv {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1) (hp : f 1=f 0) (b : Bool) :
    (∫ t in (0 : ℝ)..1,deriv f t*chamberHeightSign b t)=
      -2*(f (if b then 1/2 else 0)-f ((if b then 1/2 else 0)+1/2)) := by
  have hl : AbsolutelyContinuousOnInterval f 0 (1/2) := hf.mono (by
    rw [uIcc_of_le (by norm_num : (0 : ℝ)≤1/2),uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have hr : AbsolutelyContinuousOnInterval f (1/2) 1 := hf.mono (by
    rw [uIcc_of_le (by norm_num : (1/2 : ℝ)≤1),uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have hint : IntervalIntegrable (fun t : ℝ => deriv f t*chamberHeightSign b t) volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact hf.intervalIntegrable_deriv.def'.mul_bdd
      ((measurable_chamberHeightSign b).comp (AddCircle.continuous_mk' (1 : ℝ)).measurable).aestronglyMeasurable
      (Eventually.of_forall fun t => (norm_chamberHeightSign b t).le)
  have hli : (∫ t in (0 : ℝ)..1/2,deriv f t*chamberHeightSign b t)=
      (f (1/2)-f 0)*(if b then -1 else 1) := by
    calc
      _=∫ t in (0 : ℝ)..1/2,deriv f t*(if b then -1 else 1) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro t ht
        dsimp only
        rw [chamberHeightSign_left b ht]
      _=_ := by rw [intervalIntegral.integral_mul_const,hl.integral_deriv_eq_sub]
  have hri : (∫ t in (1/2 : ℝ)..1,deriv f t*chamberHeightSign b t)=
      (f 1-f (1/2))*(if b then 1 else -1) := by
    calc
      _=∫ t in (1/2 : ℝ)..1,deriv f t*(if b then 1 else -1) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro t ht
        dsimp only
        rw [chamberHeightSign_right b ht]
      _=_ := by rw [intervalIntegral.integral_mul_const,hr.integral_deriv_eq_sub]
  have hml : uIcc (0 : ℝ) (1/2)⊆uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ)≤1/2),uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hmr : uIcc (1/2 : ℝ) 1⊆uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (1/2 : ℝ)≤1),uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact Icc_subset_Icc (by norm_num) le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set hml) (hint.mono_set hmr),hli,hri,hp]
  cases b <;> norm_num [hp] <;> ring

end CubicTorus

end
end

end OAI
