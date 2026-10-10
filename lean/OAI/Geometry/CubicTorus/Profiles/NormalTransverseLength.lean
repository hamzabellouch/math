import Mathlib
import OAI.Geometry.CubicTorus.Reflection.ActualAxialFlux

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nonstandard_missing_neighbor_flux {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 → Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) (i : Fin 3)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    0<H ∧ V≤1/2 ∧ axialTransverseMass μ i=H*V := by
  have hc : IsPreconnected (frontier (openRepresentative E)) :=
    (Periodic.isMinimizerAt_connected_or_standard_slab hV hmin).resolve_right (fun h ↦ hstd h.2.2)
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have ho := openRepresentative_congr_ae hFE
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by rwa [ho]
  have hRF (j : Fin 3) : F=ᵐ[torusVolume]((axisReflection j).torus ⁻¹' F) :=
    hFE.trans ((hR j).trans ((axisReflection j).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hFE.symm))
  have hdF : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative F →quotientMap x∈openRepresentative F := by rwa [ho]
  have hvF : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative F := by rwa [ho]
  have hμF := hμ.congr_ae hFE.symm
  have hflux := isMinimizerAt_missing_neighbor_flux_unrestricted hV hF hmF hRF b hdF hμF
    (Periodic.coordinateCMC_of_global hμF hCMC) i hvF
  obtain ⟨N,hN,hp,hae,_⟩ := isMinimizerAt_stationary_tubular_normal hV hF hmF hμF hCMC
  have hpos := isMinimizerAt_connected_transverse_mass_pos hV hF hmF hcF hμF hN hp hae i
  have hHpos : 0<H := by
    rw [hflux] at hpos
    exact (mul_pos_iff_of_pos_right hV.1).mp hpos
  exact ⟨hHpos,isMinimizerAt_missing_neighbor_volume_le_half hV hF hmF hcF hRF b hdF i hvF,hflux⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_missing_neighbor_top_empty {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    axialSlice (openRepresentative E) i (octantHeight b i 1 : AxisCircle)=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact isMinimizerAt_missing_neighbor_gap hV hmin hR b hd i hv
    ((torusAxialSplit i).symm ((octantHeight b i 1 : AxisCircle),y)) (subset_closure hy)
    (torusAxialSplit_symm_same _ _ _)

theorem isMinimizerAt_missing_neighbor_projection {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    s^2 ≤ ((perimeter E).toReal/2)*((perimeter E).toReal/2-(H/2)*V) := by
  dsimp only
  let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
  have hz : (axialSliceVolume (openRepresentative E) i (octantHeight b i 1 : AxisCircle)).toReal=0 := by
    rw [axialSliceVolume,isMinimizerAt_missing_neighbor_top_empty hV hmin hR b hd i hv,measure_empty,ENNReal.toReal_zero]
  have hh := isMinimizerAt_actual_projection_bound hV hE hmin hμ i ha
  have hdiff : |(axialSliceVolume (openRepresentative E) i ((1/2 : ℝ) : AxisCircle)).toReal-
      (axialSliceVolume (openRepresentative E) i 0).toReal|=s := by
    dsimp only [s,Measure.real,axialSliceVolume] at hz ⊢
    unfold octantHeight at hz ⊢
    cases hb : b i <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] at hz ⊢
    · norm_num [AddCircle.coe_period] at hz ⊢
      rw [hz,zero_sub,abs_neg,abs_of_nonneg ENNReal.toReal_nonneg]
    · norm_num [AddCircle.coe_period] at hz ⊢
      rw [hz,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg]
  rw [hdiff] at hh
  have hr : 0 ≤ (μ.mass : ℝ)*((μ.mass : ℝ)-axialTransverseMass μ i) := by
    apply mul_nonneg (NNReal.coe_nonneg _)
    rw [axialTransverseMass_defect]
    simp only [sub_sub_cancel]
    exact integral_nonneg (fun _ ↦ sq_nonneg _)
  have hs : 0 ≤ s := measureReal_nonneg
  have hh2 := pow_le_pow_left₀ (by positivity : 0 ≤ 2*s) hh 2
  rw [Real.sq_sqrt hr,hμ.1,isMinimizerAt_missing_neighbor_flux_unrestricted hV hE hmin hR b hd hμ hH i hv] at hh2
  change s^2 ≤ _
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_no_face_pattern {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 → Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3)
    (hface : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then false else true))∈openRepresentative E) :
    quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∈openRepresentative E := by
  classical
  by_contra haxis
  obtain ⟨z,hzb,hseam⟩ := connected_reflected_boundary_meets_axial_seam hc
    (isMinimizerAt_frontier_nonempty_null hV hmin) (reflection_invariant_frontier hmin.1.1 hR) i
  let x := upperFold z
  have hx := upperFold_mem z
  have hxb : quotientMap x∈frontier (openRepresentative E) :=
    (upperFold_phase (reflection_invariant_frontier hmin.1.1 hR) z).mpr hzb
  let u := orientedUpperVertex b (fun j ↦ if j=i then false else true)
  let v := orientedUpperVertex b (fun j ↦ if j=i then true else false)
  have hmincase : x i=(if b i then (1/2 : ℝ) else 1) → False := by
    intro hxi
    have hxu : OrientedCoordinateLE b x u := by
      intro j
      by_cases hji : j=i
      · subst j
        dsimp only [u,orientedUpperVertex,upperVertex]
        simp only [ite_true,Bool.not_false]
        rw [hxi]
        cases b i <;> simp
      · have hh := orientedUpperVertex_max b hx j
        have hu : u j=orientedUpperVertex b (fun _ ↦ true) j := by
          dsimp [u,orientedUpperVertex,upperVertex]; simp [hji]
        change (if b j then x j≤u j else u j≤x j)
        rw [hu]
        exact hh
    have hxo := isMinimizerAt_closed_octant_order hV hmin hR hd hx (upperVertex_mem _) hxu hface
    rw [(isOpen_openRepresentative E).frontier_eq] at hxb
    exact hxb.2 hxo
  have hmaxcase : x i=(if b i then (1 : ℝ) else 1/2) → False := by
    intro hxi
    have hvx : OrientedCoordinateLE b v x := by
      intro j
      by_cases hji : j=i
      · subst j
        dsimp only [v,orientedUpperVertex,upperVertex]
        simp only [ite_true,Bool.not_true]
        rw [hxi]
        cases b i <;> simp
      · have hh := orientedUpperVertex_min b hx j
        have hv : v j=orientedUpperVertex b (fun _ ↦ false) j := by
          dsimp [v,orientedUpperVertex,upperVertex]; simp [hji]
        change (if b j then v j≤x j else x j≤v j)
        rw [hv]
        exact hh
    have hvcl := octant_downset_closure (isOpen_openRepresentative E)
      (reflection_invariant_openRepresentative hmin.1.1 hR) hd (upperVertex_mem _) hx hvx
      (frontier_subset_closure hxb)
    have hvb : quotientMap v∈frontier (openRepresentative E) := by
      rw [(isOpen_openRepresentative E).frontier_eq]
      exact ⟨hvcl,haxis⟩
    exact isMinimizerAt_common_fixed_not_boundary hV hmin hR _ (upperVertex_fixed _) hvb
  change x i=(1/2 : ℝ) ∨ x i=1 at hseam
  cases hb : b i <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] at hmincase hmaxcase
  · exact hseam.elim hmaxcase hmincase
  · exact hseam.elim hmincase hmaxcase

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalTransverseLength (i : Fin 3) (z : NormalBundle) : ℝ :=
  Real.sqrt (1-((z.2 : Cover) i)^2)

lemma normalTransverseLength_continuous (i : Fin 3) : Continuous (normalTransverseLength i) :=
  (continuous_const.sub ((normal_component_continuous i).pow 2)).sqrt

lemma normalTransverseLength_nonneg (i : Fin 3) (z : NormalBundle) :
    0≤normalTransverseLength i z := Real.sqrt_nonneg _

lemma normalTransverseLength_sq (i : Fin 3) (z : NormalBundle) :
    (normalTransverseLength i z)^2+((z.2 : Cover) i)^2=1 := by
  rw [normalTransverseLength,Real.sq_sqrt (sub_nonneg.mpr (normalSphere_coordinate_sq_le z.2 i))]
  ring

lemma normalTransverseLength_le_one (i : Fin 3) (z : NormalBundle) :
    normalTransverseLength i z≤1 := by
  have h := normalTransverseLength_sq i z
  nlinarith [sq_nonneg ((z.2 : Cover) i)]

def axialPerimeterMarginal (μ : FiniteMeasure NormalBundle) (i : Fin 3) : FiniteMeasure AxisCircle := by
  let η := (μ : Measure NormalBundle).withDensity (fun z ↦ ENNReal.ofReal (normalTransverseLength i z))
  have hi : Integrable (normalTransverseLength i) (μ : Measure NormalBundle) :=
    (normalTransverseLength_continuous i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  haveI : IsFiniteMeasure η := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  exact ⟨Measure.map (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) η,inferInstance⟩

lemma axialPerimeterMarginal_absolutelyContinuous {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (axialPerimeterMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hh := ha hz
  change Measure.map _ _ s=0 at hh ⊢
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh ⊢
  exact withDensity_absolutelyContinuous _ _ hh

def axialPerimeterDensity (μ : FiniteMeasure NormalBundle) (i : Fin 3) (t : AxisCircle) : ℝ :=
  ((axialPerimeterMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal

lemma axialPerimeterDensity_nonneg (μ : FiniteMeasure NormalBundle) (i : Fin 3) (t : AxisCircle) :
    0≤axialPerimeterDensity μ i t := ENNReal.toReal_nonneg

lemma axialPerimeterDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialPerimeterDensity μ i) := Measure.integrable_toReal_rnDeriv

lemma axialPerimeterDensity_measurable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Measurable (axialPerimeterDensity μ i) := (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma axialPerimeterDensity_pairing_bounded {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Measurable f) (_hb : ∀ t,|f t|≤1) :
    (∫ t,axialPerimeterDensity μ i t*f t)=
      ∫ z,normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  have hp := axialPerimeterMarginal_absolutelyContinuous i ha
  change (∫ t,((axialPerimeterMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal*f t)=_
  rw [integral_toReal_rnDeriv_mul hp]
  change (∫ t,f t ∂Measure.map _ _)=_
  rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (normalTransverseLength_continuous i).measurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (normalTransverseLength_nonneg i z),smul_eq_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

lemma bounded_real_locallyIntegrable {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) : LocallyIntegrable f volume := by
  apply (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ))).locallyIntegrable.mono hf.aestronglyMeasurable
  exact ae_of_all _ fun t ↦ by simpa only [Real.norm_eq_abs,abs_one] using hb t

lemma circleSmoothApprox_bounded_contDiff {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (circleSmoothApprox f n) :=
  (circleMollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (circleMollifier n).contDiff_normed
    (bounded_real_locallyIntegrable hf hb)

lemma circleSmoothApprox_nonneg {f : ℝ → ℝ} (hf : ∀ t,0≤f t) (n : ℕ) (t : ℝ) :
    0≤circleSmoothApprox f n t := by
  rw [circleSmoothApprox,convolution_def]
  exact integral_nonneg fun x ↦ mul_nonneg ((circleMollifier n).nonneg_normed x) (hf (t-x))

lemma circleSmoothApprox_bounded_ae_tendsto {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) :
    ∀ᵐ t : ℝ,Tendsto (fun n ↦ circleSmoothApprox f n t) atTop (𝓝 (f t)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    circleMollifier_tendsto (K := 2) _ (bounded_real_locallyIntegrable hf hb)
  exact Eventually.of_forall fun n ↦ by dsimp [circleMollifier]; ring_nf; rfl

lemma circleSmoothApprox_lift_ae_tendsto {f : AxisCircle → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) :
    let F : ℝ → ℝ := fun t ↦ f (t : AxisCircle)
    let hp : Function.Periodic F 1 := fun t ↦ by dsimp only [F]; rw [AddCircle.coe_add_period]
    ∀ᵐ t : AxisCircle,Tendsto (fun n ↦ (circleSmoothApprox_periodic hp n).lift t) atTop (𝓝 (f t)) := by
  intro F hp
  have hfm : Measurable F := hf.comp (AddCircle.continuous_mk' (1 : ℝ)).measurable
  have hh := ae_restrict_of_ae (s := Ioc (0 : ℝ) 1) (circleSmoothApprox_bounded_ae_tendsto hfm (fun t ↦ hb _))
  have hmp : MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1)) volume := by
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [←hmp.map_eq]
  apply (ae_map_iff hmp.measurable.aemeasurable (measurableSet_tendsto_fun
    (fun n ↦ (continuous_periodic_lift (circleSmoothApprox_periodic hp n)
      (circleSmoothApprox_bounded_contDiff hfm (fun t ↦ hb _) n).continuous).measurable) hf)).mpr
  simpa only [Function.Periodic.lift_coe] using hh

theorem integrable_circle_nonneg_of_smooth_pairing {h : AxisCircle → ℝ} (hi : Integrable h)
    (hw : ∀ (ψ : ℝ → ℝ),ContDiff ℝ (⊤ : ℕ∞) ψ → ∀ hp : Function.Periodic ψ 1,
      (∀ t,0≤ψ t) → 0≤∫ t,h t*hp.lift t) : 0≤ᵐ[volume] h := by
  apply ae_nonneg_of_forall_setIntegral_nonneg hi
  intro s hs _
  let f : AxisCircle → ℝ := s.indicator (fun _ ↦ (1 : ℝ))
  let F : ℝ → ℝ := fun t ↦ f (t : AxisCircle)
  have hf : Measurable f := measurable_const.indicator hs
  have hb (t : AxisCircle) : |f t|≤1 := by
    by_cases ht : t∈s <;> simp [f,ht]
  have hn (t : ℝ) : 0≤F t := by apply indicator_nonneg; intro _ _; norm_num
  have hp : Function.Periodic F 1 := fun t ↦ by dsimp only [F]; rw [AddCircle.coe_add_period]
  have hc n := circleSmoothApprox_bounded_contDiff (hf.comp (AddCircle.continuous_mk' (1 : ℝ)).measurable)
    (fun t ↦ hb _) n
  have hl : Tendsto (fun n ↦ ∫ t,h t*(circleSmoothApprox_periodic hp n).lift t) atTop
      (𝓝 (∫ t,h t*f t)) := by
    apply tendsto_integral_of_dominated_convergence (fun t ↦ ‖h t‖)
    · intro n
      exact hi.aestronglyMeasurable.mul (continuous_periodic_lift (circleSmoothApprox_periodic hp n)
        (hc n).continuous).aestronglyMeasurable
    · exact hi.norm
    · intro n
      filter_upwards [] with t
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      induction t using Quotient.inductionOn with | h t =>
        exact circleSmoothApprox_bound (fun t ↦ by simpa only [Real.norm_eq_abs] using hb (t : AxisCircle)) n t
    · filter_upwards [circleSmoothApprox_lift_ae_tendsto hf hb] with t ht
      exact tendsto_const_nhds.mul ht
  have hh : 0≤∫ t,h t*f t := ge_of_tendsto hl (Eventually.of_forall fun n ↦
    hw _ (hc n) (circleSmoothApprox_periodic hp n) (circleSmoothApprox_nonneg hn n))
  have he : (fun t ↦ h t*f t)=s.indicator h := by
    funext t
    by_cases ht : t∈s <;> simp [f,ht]
  rwa [he,integral_indicator hs] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSliceIntegral (E : Set Torus) (i : Fin 3) (f : Torus → ℝ) (t : AxisCircle) : ℝ :=
  ∫ y in axialSlice E i t,f ((torusAxialSplit i).symm (t,y))

lemma axialSliceIntegral_indicator {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (f : Torus → ℝ) (t : AxisCircle) :
    axialSliceIntegral E i f t=∫ y,E.indicator f ((torusAxialSplit i).symm (t,y)) := by
  rw [axialSliceIntegral,←integral_indicator (axialSlice_measurable hE i t)]
  congr 1

lemma axialSliceIntegral_integrable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {f : Torus → ℝ} (hf : Integrable f torusVolume) : Integrable (axialSliceIntegral E i f) := by
  have hg := (torusAxialSplit_measurePreserving i).symm.integrable_comp_of_integrable (hf.indicator hE)
  have hh := hg.integral_prod_left
  simpa only [Function.comp_apply,←axialSliceIntegral_indicator hE] using hh

lemma axialSliceIntegral_pairing {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {f : Torus → ℝ} (hf : Continuous f) {ψ : AxisCircle → ℝ} (hψ : Continuous ψ) :
    (∫ t,ψ t*axialSliceIntegral E i f t)=∫ z in E,ψ (z i)*f z ∂torusVolume := by
  have hi : Integrable (fun z : Torus ↦ ψ (z i)*f z) torusVolume :=
    ((hψ.comp (PiLp.continuous_apply 2 _ i)).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg := (torusAxialSplit_measurePreserving i).symm.integrable_comp_of_integrable (hi.indicator hE)
  rw [←integral_indicator hE,←(torusAxialSplit_measurePreserving i).symm.integral_comp'
    (E.indicator (fun z : Torus ↦ ψ (z i)*f z))]
  change _=∫ z,((E.indicator (fun z : Torus ↦ ψ (z i)*f z)) ∘ (torusAxialSplit i).symm) z ∂volume.prod volume
  rw [integral_prod _ hg]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [axialSliceIntegral_indicator hE,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : (torusAxialSplit i).symm (t,y)∈E <;> simp [hy]

lemma normal_transverse_inner_bound (i : Fin 3) (z : NormalBundle) (v : Cover)
    (hv : v i=0) (hb : ‖v‖≤1) : ⟪(z.2 : Cover),v⟫≤normalTransverseLength i z := by
  let n : Cover := (z.2 : Cover)-((z.2 : Cover) i) • EuclideanSpace.single i 1
  have hn : ‖n‖=normalTransverseLength i z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (normalTransverseLength_nonneg i z)).mp
    have hz : ‖(z.2 : Cover)‖=1 := z.2.property
    have hs := normalTransverseLength_sq i z
    dsimp only [n]
    rw [norm_sub_sq_real,real_inner_smul_right,EuclideanSpace.inner_single_right,norm_smul,
      PiLp.norm_single,Real.norm_eq_abs,Real.norm_eq_abs,abs_one,mul_one,hz]
    simp only [conj_trivial,one_mul] at *
    nlinarith [sq_abs ((z.2 : Cover) i)]
  have he : ⟪n,v⟫=⟪(z.2 : Cover),v⟫ := by
    simp [n,inner_sub_left,real_inner_smul_left,EuclideanSpace.inner_single_left,hv]
  rw [←he]
  calc
    _ ≤ ‖n‖*‖v‖ := real_inner_le_norm _ _
    _ ≤ ‖n‖ := mul_le_of_le_one_right (norm_nonneg _) hb
    _ = _ := hn

lemma axialPerimeterDensity_pairing_continuous {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,axialPerimeterDensity μ i t*f t)=
      ∫ z,normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  have hp := axialPerimeterMarginal_absolutelyContinuous i ha
  change (∫ t,((axialPerimeterMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal*f t)=_
  rw [integral_toReal_rnDeriv_mul hp]
  change (∫ t,f t ∂Measure.map _ _)=_
  rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (normalTransverseLength_continuous i).measurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (normalTransverseLength_nonneg i z),smul_eq_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axial_weight_divergence {i : Fin 3} {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFi : ∀ x,F x i=0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Cover) :
    divergence (fun y : Cover ↦ ψ (y i) • F y) x=ψ (x i)*divergence F x := by
  have hd : DifferentiableAt ℝ (fun y : Cover ↦ ψ (y i)) x :=
    ((hψ.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).differentiable (by simp)).differentiableAt
  rw [divergence_smul_function hd
    (hF.differentiable (by simp)).differentiableAt,inner_gradient_left,
    axial_scalar_fderiv (hψ.differentiable (by simp)),hFi,mul_zero,add_zero]

theorem axialSliceIntegral_weighted_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {F : Cover → Cover} (hF : AdmissibleField F) (hFi : ∀ x,F x i=0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1)
    (hn : ∀ t,0≤ψ t) :
    (∫ t,hp.lift t*axialSliceIntegral E i (fun z ↦ divergence F (representative z)) t)≤
      ∫ t,hp.lift t*axialPerimeterDensity μ i t := by
  let G : Cover → Cover := fun x ↦ ψ (x i) • F x
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (hψ.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).smul hF.1
  have hGp : ∀ m x,G (x+latticeVector m)=G x := by
    intro m x
    dsimp only [G]
    rw [axial_scalar_periodic hp i m x,hF.2.1]
  obtain ⟨C,hC,hCb⟩ := periodic_bounded hG.continuous hGp
  have hflux := normalMeasure_flux hμ hG hGp (show 0<C+1 by linarith) (fun x ↦ (hCb x).trans (by linarith))
  have hd : Continuous (fun z : Torus ↦ divergence F (representative z)) :=
    continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  have hp' := continuous_periodic_lift hp hψ.continuous
  rw [axialSliceIntegral_pairing hE i hd hp']
  have he : (fun z : Torus ↦ hp.lift (z i)*divergence F (representative z))=
      (fun z : Torus ↦ divergence G (representative z)) := by
    funext z
    rw [axial_weight_divergence hF.1 hFi hψ]
    congr 1
    have hh := congrArg (fun a : Torus ↦ hp.lift (a i)) (quotientMap_representative z)
    exact hh.symm
  rw [he,setIntegral_lift (continuous_divergence hG) (divergence_periodic hGp) hE,←hflux]
  simp_rw [mul_comm (hp.lift _) (axialPerimeterDensity μ i _)]
  rw [axialPerimeterDensity_pairing_continuous i ha hp']
  apply integral_mono
  · exact (normalTest G hG.continuous).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact ((normalTransverseLength_continuous i).mul (hp'.comp (normal_axisCircle_continuous i))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro z
    change ⟪(z.2 : Cover),ψ ((z.1 : Cover) i) • F z.1⟫≤_
    simp only [real_inner_smul_right,Function.Periodic.lift_coe]
    rw [mul_comm (normalTransverseLength i z)]
    exact mul_le_mul_of_nonneg_left (normal_transverse_inner_bound i z _ (hFi _) (hF.2.2 _)) (hn _)

theorem axialSliceIntegral_ae_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {F : Cover → Cover} (hF : AdmissibleField F) (hFi : ∀ x,F x i=0) :
    axialSliceIntegral E i (fun z ↦ divergence F (representative z))≤ᵐ[volume]axialPerimeterDensity μ i := by
  have hd : Continuous (fun z : Torus ↦ divergence F (representative z)) :=
    continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  have hdI := hd.integrable_of_hasCompactSupport (μ := torusVolume) (HasCompactSupport.of_compactSpace _)
  have hs := axialSliceIntegral_integrable hE i hdI
  have hi := axialPerimeterDensity_integrable μ i
  have hh := integrable_circle_nonneg_of_smooth_pairing (hi.sub hs) (by
    intro ψ hψ hp hn
    have hc := continuous_periodic_lift hp hψ.continuous
    simp only [Pi.sub_apply,sub_mul]
    rw [integral_sub (circle_integrable_mul_continuous hi hc) (circle_integrable_mul_continuous hs hc)]
    apply sub_nonneg.mpr
    simpa only [mul_comm] using axialSliceIntegral_weighted_le hE hμ i ha hF hFi hψ hp hn)
  filter_upwards [hh] with t ht
  exact sub_nonneg.mp ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSection_integrable (E : Set Torus) (i : Fin 3) (t : AxisCircle) (f : C(Torus,ℝ)) :
    Integrable (fun y : TransverseProduct ↦ f ((torusAxialSplit i).symm (t,y)))
      (volume.restrict (axialSlice E i t)) := by
  apply Integrable.of_bound
    (f.continuous.measurable.comp ((torusAxialSplit i).symm.measurable.comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable ‖f‖
  exact ae_of_all _ fun y ↦ f.norm_coe_le_norm _

def axialSliceFunctional (E : Set Torus) (i : Fin 3) (t : AxisCircle) : C(Torus,ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ axialSliceIntegral E i f t
      map_add' := by
        intro f g
        exact integral_add (axialSection_integrable E i t f) (axialSection_integrable E i t g)
      map_smul' := by
        intro c f
        exact integral_const_mul c (fun y : TransverseProduct ↦ f ((torusAxialSplit i).symm (t,y))) }
    1 (by
      intro f
      have hh := norm_setIntegral_le_of_norm_le_const (measure_lt_top volume (axialSlice E i t))
        (fun y (_ : y∈axialSlice E i t) ↦ f.norm_coe_le_norm ((torusAxialSplit i).symm (t,y)))
      have hm : (volume (axialSlice E i t)).toReal≤1 := by
        simpa only [axialSliceVolume,ENNReal.toReal_one] using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞)≠∞) (axialSliceVolume_le_one E i t)
      change ‖axialSliceIntegral E i f t‖≤1*‖f‖
      simpa only [one_mul,axialSliceIntegral] using hh.trans (mul_le_of_le_one_right (norm_nonneg f) hm))

def axialDivergenceClass (i : Fin 3) : Set C(Torus,ℝ) :=
  {f | ∃ (F : Cover → Cover) (hF : AdmissibleField F),
    (∀ x,F x i=0) ∧ f=⟨fun z ↦ divergence F (representative z),
      continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)⟩}

theorem axialSliceIntegral_ae_all_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    ∀ᵐ t : AxisCircle,∀ (F : Cover → Cover) (_hF : AdmissibleField F),
      (∀ x,F x i=0) →
      axialSliceIntegral E i (fun z ↦ divergence F (representative z)) t≤axialPerimeterDensity μ i t := by
  obtain ⟨S,hS,hSc,hSd⟩ := (TopologicalSpace.IsSeparable.of_separableSpace (axialDivergenceClass i)).exists_countable_dense_subset
  have hh : ∀ f∈S,∀ᵐ t : AxisCircle,axialSliceFunctional E i t f≤axialPerimeterDensity μ i t := by
    intro f hf
    obtain ⟨F,hF,hFi,rfl⟩ := hS hf
    exact axialSliceIntegral_ae_le hE hμ i ha hF hFi
  filter_upwards [(ae_ball_iff hSc).mpr hh] with t ht
  intro F hF hFi
  let f : C(Torus,ℝ) := ⟨fun z ↦ divergence F (representative z),
    continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)⟩
  have hf : f∈axialDivergenceClass i := ⟨F,hF,hFi,rfl⟩
  have hc : IsClosed {f : C(Torus,ℝ) | axialSliceFunctional E i t f≤axialPerimeterDensity μ i t} :=
    isClosed_le (axialSliceFunctional E i t).continuous continuous_const
  exact (closure_minimal ht hc) (hSd hf)

def axialTestPerimeter (E : Set Torus) (i : Fin 3) (t : AxisCircle) : ℝ≥0∞ :=
  ⨆ (F : Cover → Cover) (_ : AdmissibleField F) (_ : ∀ x,F x i=0),
    ENNReal.ofReal (axialSliceIntegral E i (fun z ↦ divergence F (representative z)) t)

theorem axialTestPerimeter_ae_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    ∀ᵐ t : AxisCircle,axialTestPerimeter E i t≤ENNReal.ofReal (axialPerimeterDensity μ i t) := by
  filter_upwards [axialSliceIntegral_ae_all_le hE hμ i ha] with t ht
  exact iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hFi ↦ ENNReal.ofReal_le_ofReal (ht F hF hFi)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeAxisEmbedding (i : Fin 3) : Plane →L[ℝ] Cover :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y ↦ WithLp.toLp 2 (i.insertNth 0 y.ofLp)
      map_add' := by
        intro x y; ext j
        rcases Fin.eq_self_or_eq_succAbove i j with rfl|⟨k,rfl⟩ <;> simp
      map_smul' := by
        intro a x; ext j
        rcases Fin.eq_self_or_eq_succAbove i j with rfl|⟨k,rfl⟩ <;> simp }

def planeAxisProjection (i : Fin 3) : Cover →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ WithLp.toLp 2 (fun j ↦ x (i.succAbove j))
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }

@[simp] lemma planeAxisEmbedding_same (i : Fin 3) (y : Plane) :
    planeAxisEmbedding i y i=0 := by
  change i.insertNth (α := fun _ : Fin 3 ↦ ℝ) 0 y.ofLp i=0
  exact Fin.insertNth_apply_same (α := fun _ : Fin 3 ↦ ℝ) i 0 y.ofLp
@[simp] lemma planeAxisEmbedding_succAbove (i : Fin 3) (y : Plane) (j : Fin 2) :
    planeAxisEmbedding i y (i.succAbove j)=y j := by
  change i.insertNth (α := fun _ : Fin 3 ↦ ℝ) 0 y.ofLp (i.succAbove j)=y j
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 ↦ ℝ) i 0 y.ofLp j
@[simp] lemma planeAxisProjection_apply (i : Fin 3) (x : Cover) (j : Fin 2) :
    planeAxisProjection i x j=x (i.succAbove j) := rfl

lemma planeAxisEmbedding_norm (i : Fin 3) (y : Plane) : ‖planeAxisEmbedding i y‖=‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succAbove _ i]
  simp

lemma planeAxisProjection_norm_le (i : Fin 3) (x : Cover) : ‖planeAxisProjection i x‖≤‖x‖ := by
  have hh : ‖planeAxisProjection i x‖^2≤‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succAbove _ i]
    simp only [planeAxisProjection_apply]
    nlinarith [sq_nonneg ‖x i‖]
  nlinarith [norm_nonneg (planeAxisProjection i x),norm_nonneg x]

@[simp] lemma planeAxisProjection_embedding (i : Fin 3) (y : Plane) :
    planeAxisProjection i (planeAxisEmbedding i y)=y := by ext j; simp

@[simp] lemma planeAxisProjection_single_same (i : Fin 3) :
    planeAxisProjection i (EuclideanSpace.single i 1)=0 := by
  ext j
  simp [Fin.succAbove_ne]

@[simp] lemma planeAxisProjection_single_succAbove (i : Fin 3) (j : Fin 2) :
    planeAxisProjection i (EuclideanSpace.single (i.succAbove j) 1)=EuclideanSpace.single j 1 := by
  ext k
  simp [Fin.succAbove_right_injective.eq_iff]

def PlanarAdmissibleField (G : Plane → Plane) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) G ∧
  (∀ (n : Fin 2 → ℤ) (y : Plane),G (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=G y) ∧
  ∀ y,‖G y‖≤1

def liftPlanarField (i : Fin 3) (G : Plane → Plane) (x : Cover) : Cover :=
  planeAxisEmbedding i (G (planeAxisProjection i x))

lemma liftPlanarField_admissible (i : Fin 3) {G : Plane → Plane}
    (hG : PlanarAdmissibleField G) : AdmissibleField (liftPlanarField i G) := by
  refine ⟨(planeAxisEmbedding i).contDiff.comp (hG.1.comp (planeAxisProjection i).contDiff),?_,?_⟩
  · intro n x
    unfold liftPlanarField
    rw [map_add]
    exact congrArg (planeAxisEmbedding i) (hG.2.1 (fun j ↦ n (i.succAbove j)) _)
  · intro x
    rw [liftPlanarField,planeAxisEmbedding_norm]
    exact hG.2.2 _

@[simp] lemma liftPlanarField_same (i : Fin 3) (G : Plane → Plane) (x : Cover) :
    liftPlanarField i G x i=0 := planeAxisEmbedding_same _ _

lemma divergence_liftPlanarField (i : Fin 3) {G : Plane → Plane}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Cover) :
    divergence (liftPlanarField i G) x=planeDivergence G (planeAxisProjection i x) := by
  have hd := (planeAxisEmbedding i).hasFDerivAt.comp x
    (((hG.differentiable (by simp) (planeAxisProjection i x)).hasFDerivAt).comp x
      (planeAxisProjection i).hasFDerivAt)
  change HasFDerivAt (liftPlanarField i G) _ x at hd
  rw [divergence,hd.fderiv,Fin.sum_univ_succAbove _ i]
  simp [ContinuousLinearMap.comp_apply,planeDivergence,Fin.sum_univ_two]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

@[simp] lemma planeAxisEmbedding_single (i : Fin 3) (j : Fin 2) :
    planeAxisEmbedding i (EuclideanSpace.single j 1)=EuclideanSpace.single (i.succAbove j) 1 := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨k,rfl⟩
  · simp
  · simp [Fin.succAbove_right_injective.eq_iff]

def planeAxisAt (i : Fin 3) (a : ℝ) (y : Plane) : Cover :=
  a • EuclideanSpace.single i 1+planeAxisEmbedding i y

@[simp] lemma planeAxisAt_same (i : Fin 3) (a : ℝ) (y : Plane) : planeAxisAt i a y i=a := by
  simp [planeAxisAt]
@[simp] lemma planeAxisAt_succAbove (i : Fin 3) (a : ℝ) (y : Plane) (j : Fin 2) :
    planeAxisAt i a y (i.succAbove j)=y j := by
  simp [planeAxisAt,Fin.succAbove_ne]

lemma planeAxisAt_contDiff (i : Fin 3) (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (planeAxisAt i a) :=
  contDiff_const.add (planeAxisEmbedding i).contDiff

lemma planeAxisAt_hasFDerivAt (i : Fin 3) (a : ℝ) (y : Plane) :
    HasFDerivAt (planeAxisAt i a) (planeAxisEmbedding i) y := by
  exact (planeAxisEmbedding i).hasFDerivAt.const_add (a • EuclideanSpace.single i (1 : ℝ))

def tracePlanarField (i : Fin 3) (a : ℝ) (F : Cover → Cover) (y : Plane) : Plane :=
  planeAxisProjection i (F (planeAxisAt i a y))

lemma tracePlanarField_admissible (i : Fin 3) (a : ℝ) {F : Cover → Cover}
    (hF : AdmissibleField F) : PlanarAdmissibleField (tracePlanarField i a F) := by
  refine ⟨(planeAxisProjection i).contDiff.comp (hF.1.comp (planeAxisAt_contDiff i a)),?_,?_⟩
  · intro n y
    have he : planeAxisAt i a (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=
        planeAxisAt i a y+latticeVector (i.insertNth (α := fun _ : Fin 3 ↦ ℤ) 0 n) := by
      ext k
      rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨k,rfl⟩ <;>
        simp [latticeVector,planeAxisAt,map_add,add_assoc]
    unfold tracePlanarField
    rw [he,hF.2.1]
  · intro y
    exact (planeAxisProjection_norm_le i _).trans (hF.2.2 _)

lemma planeDivergence_tracePlanarField (i : Fin 3) (a : ℝ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFi : ∀ x,F x i=0) (y : Plane) :
    planeDivergence (tracePlanarField i a F) y=divergence F (planeAxisAt i a y) := by
  have hd := (planeAxisProjection i).hasFDerivAt.comp y
    (((hF.differentiable (by simp) (planeAxisAt i a y)).hasFDerivAt).comp y
      (planeAxisAt_hasFDerivAt i a y))
  change HasFDerivAt (tracePlanarField i a F) _ y at hd
  have hz : (fderiv ℝ F (planeAxisAt i a y) (EuclideanSpace.single i 1)) i=0 := by
    rw [←fderiv_component (hF.differentiable (by simp) _) i]
    simp only [hFi]
    simp
  rw [planeDivergence,hd.fderiv,divergence,Fin.sum_univ_succAbove _ i,hz]
  simp [ContinuousLinearMap.comp_apply,Fin.sum_univ_two]

def planarRepresentative (y : TransverseProduct) : Plane :=
  WithLp.toLp 2 (fun j ↦ ((AddCircle.equivIco (1 : ℝ) 0) (y j) : ℝ))

lemma planeAxisProjection_representative (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    planeAxisProjection i (representative ((torusAxialSplit i).symm (t,y)))=planarRepresentative y := by
  ext j
  simp [representative,planarRepresentative]

lemma representative_axialSplit (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    representative ((torusAxialSplit i).symm (t,y))=
      planeAxisAt i (((AddCircle.equivIco (1 : ℝ) 0) t) : ℝ) (planarRepresentative y) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨k,rfl⟩ <;>
    simp [representative,planarRepresentative]

def planarTorusPerimeter (A : Set TransverseProduct) : ℝ≥0∞ :=
  ⨆ (G : Plane → Plane) (_ : PlanarAdmissibleField G),
    ENNReal.ofReal (∫ y in A,planeDivergence G (planarRepresentative y))

theorem axialTestPerimeter_eq_planar (E : Set Torus) (i : Fin 3) (t : AxisCircle) :
    axialTestPerimeter E i t=planarTorusPerimeter (axialSlice E i t) := by
  apply le_antisymm
  · refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hFi ↦ ?_
    let a : ℝ := ((AddCircle.equivIco (1 : ℝ) 0) t : ℝ)
    have hb : ENNReal.ofReal (∫ y in axialSlice E i t,
        planeDivergence (tracePlanarField i a F) (planarRepresentative y))≤
        planarTorusPerimeter (axialSlice E i t) :=
      le_iSup_of_le (tracePlanarField i a F)
        (le_iSup_of_le (tracePlanarField_admissible i a hF) le_rfl)
    apply le_trans _ hb
    apply le_of_eq
    congr 1
    unfold axialSliceIntegral
    apply integral_congr_ae
    filter_upwards [] with y
    rw [planeDivergence_tracePlanarField i a hF.1 hFi,representative_axialSplit]
  · refine iSup_le fun G ↦ iSup_le fun hG ↦ ?_
    have hb : ENNReal.ofReal (axialSliceIntegral E i
        (fun z ↦ divergence (liftPlanarField i G) (representative z)) t)≤axialTestPerimeter E i t :=
      le_iSup_of_le (liftPlanarField i G)
        (le_iSup_of_le (liftPlanarField_admissible i hG)
          (le_iSup_of_le (liftPlanarField_same i G) le_rfl))
    apply le_trans _ hb
    apply le_of_eq
    congr 1
    unfold axialSliceIntegral
    apply integral_congr_ae
    filter_upwards [] with y
    rw [divergence_liftPlanarField i hG.1,planeAxisProjection_representative]

theorem planarTorusPerimeter_slice_ae_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    ∀ᵐ t : AxisCircle,planarTorusPerimeter (axialSlice E i t)≤ENNReal.ofReal (axialPerimeterDensity μ i t) := by
  simpa only [axialTestPerimeter_eq_planar] using axialTestPerimeter_ae_le hE hμ i ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarAxialField (j : Fin 2) (ψ : ℝ → ℝ) (y : Plane) : Plane :=
  ψ (y j) • EuclideanSpace.single j 1

end CubicTorus
end
end
end

end OAI
