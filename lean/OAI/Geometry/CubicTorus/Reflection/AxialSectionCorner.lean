import Mathlib
import OAI.Geometry.CubicTorus.Profiles.NormalTransverseLength

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarAxialField_admissible (j : Fin 2) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1)
    (hb : ∀ t,|ψ t|≤1) : PlanarAdmissibleField (planarAxialField j ψ) := by
  refine ⟨(hψ.comp (EuclideanSpace.proj j : Plane →L[ℝ] ℝ).contDiff).smul contDiff_const,?_,?_⟩
  · intro n y
    unfold planarAxialField
    congr 1
    simpa using hp.int_mul (n j) (y j)
  · intro y
    simpa only [planarAxialField,norm_smul,PiLp.norm_single,Real.norm_eq_abs,
      abs_one,mul_one] using hb (y j)

lemma planeDivergence_planarAxialField (j : Fin 2) {ψ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (y : Plane) :
    planeDivergence (planarAxialField j ψ) y=deriv ψ (y j) := by
  have hds := (hψ (y j)).hasDerivAt.comp_hasFDerivAt y
    (EuclideanSpace.proj j : Plane →L[ℝ] ℝ).hasFDerivAt
  have hd := hds.smul_const (EuclideanSpace.single j (1 : ℝ))
  change HasFDerivAt (planarAxialField j ψ) _ y at hd
  rw [planeDivergence,hd.fderiv]
  fin_cases j <;> simp [ContinuousLinearMap.smulRight_apply]

lemma planarAxialField_flux (A : Set TransverseProduct) (j : Fin 2) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1) :
    (∫ y in A,planeDivergence (planarAxialField j ψ) (planarRepresentative y))=
      ∫ y in A,(real_periodic_deriv hp).lift (y j) := by
  apply integral_congr_ae
  filter_upwards [] with y
  rw [planeDivergence_planarAxialField j (hψ.differentiable (by simp))]
  have he := (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (y j)
  change (((AddCircle.equivIco (1 : ℝ) 0) (y j) : ℝ) : AxisCircle)=y j at he
  conv_rhs => rw [←he]
  rfl

theorem planarTorusPerimeter_ge_axial_flux (A : Set TransverseProduct) (j : Fin 2)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1)
    (hb : ∀ t,|ψ t|≤1) :
    ENNReal.ofReal (∫ y in A,(real_periodic_deriv hp).lift (y j))≤planarTorusPerimeter A := by
  rw [←planarAxialField_flux A j hψ hp]
  exact le_iSup_of_le (planarAxialField j ψ)
    (le_iSup_of_le (planarAxialField_admissible j hψ hp hb) le_rfl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circlePeriodize_integral_short {f : ℝ → ℝ}
    (hc : HasCompactSupport f) {d : ℝ}
    (hs : tsupport f ⊆ Ioo (d-1/2) (d+1/2)) :
    (∫ t : AxisCircle,(circlePeriodize_periodic f).lift t)=∫ t : ℝ,f t := by
  rw [←AddCircle.intervalIntegral_preimage (1 : ℝ) (d-1/2),show d-1/2+1=d+1/2 by ring]
  calc
    _=∫ t in (d-1/2)..d+1/2,f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (circlePeriodize_eventuallyEq hc hs (by
        simpa only [uIcc_of_le (show d-1/2≤d+1/2 by linarith)] using ht)).eq_of_nhds
    _=∫ t : ℝ,f t := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      exact image_eq_zero_of_notMem_tsupport (fun hh ↦ ht ⟨(hs hh).1,(hs hh).2.le⟩)

theorem planarTorusPerimeter_ge_two_of_bump_strips
    {A : Set TransverseProduct} (hA : MeasurableSet A) (j : Fin 2)
    {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbi : Integrable b volume)
    (hb0 : ∀ t,0≤b t) (hb1 : ∫ t,b t=1)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a≤c)
    (hshort : c-a+2*r<1)
    (hin : ∀ t : ℝ,b (t-a)≠0 → ∀ y : TransverseProduct,y j=(t : AxisCircle) → y∈A)
    (hout : ∀ t : ℝ,b (t-c)≠0 → ∀ y : TransverseProduct,y j=(t : AxisCircle) → y∉A) :
    (2 : ℝ≥0∞)≤planarTorusPerimeter A := by
  let H := intervalSmoothHat b a c
  let d := (a+c)/2
  have hHs : tsupport H ⊆ Ioo (d-1/2) (d+1/2) := by
    apply (intervalSmoothHat_support hb.continuous hs hac).trans
    intro x hx
    dsimp only [d]
    constructor <;> linarith [hx.1,hx.2]
  have hHc : HasCompactSupport H :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport H)
      (intervalSmoothHat_support hb.continuous hs hac)
  let B : ℝ → ℝ := fun t ↦ b (t-a)
  have hBs : tsupport B ⊆ Ioo (d-1/2) (d+1/2) := by
    intro t ht
    have hh := hs (tsupport_comp_subset_preimage b (continuous_id.sub continuous_const) ht)
    change -r≤t-a ∧ t-a≤r at hh
    dsimp only [d]
    constructor <;> linarith [hh.1,hh.2]
  have hBc : HasCompactSupport B :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport B)
      (fun _ ht ↦ ⟨(hBs ht).1.le,(hBs ht).2.le⟩)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hb.comp (contDiff_id.sub contDiff_const)
  let ψ : ℝ → ℝ := fun t ↦ 2*circlePeriodize H t-1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (contDiff_const.mul (circlePeriodize_contDiff (intervalSmoothHat_contDiff hb a c) hHc)).sub contDiff_const
  have hp : Function.Periodic ψ 1 := fun t ↦ by
    dsimp only [ψ]
    rw [circlePeriodize_periodic H t]
  have hbψ (t : ℝ) : |ψ t|≤1 := by
    have hh := circlePeriodize_unit_bounds hHs (fun t ↦
      ⟨intervalSmoothHat_nonneg hb.continuous hb0 hac t,
        intervalSmoothHat_le_one hb.continuous hbi hb0 hb1 hac t⟩) t
    apply abs_le.mpr
    dsimp only [ψ]
    constructor <;> linarith [hh.1,hh.2]
  have hd (t : ℝ) (ht : t∈Icc (d-1/2) (d+1/2)) : deriv ψ t=2*(b (t-a)-b (t-c)) := by
    have he := circlePeriodize_eventuallyEq hHc hHs ht
    dsimp only [ψ]
    rw [deriv_sub_const,deriv_const_mul 2
      ((circlePeriodize_contDiff (intervalSmoothHat_contDiff hb a c) hHc).differentiable (by simp) t),
      he.deriv_eq,(intervalSmoothHat_hasDerivAt hb.continuous a c t).deriv]
  let β : AxisCircle → ℝ := (circlePeriodize_periodic B).lift
  have hβ : Continuous β := continuous_periodic_lift _ (circlePeriodize_contDiff hB hBc).continuous
  have hβi : (∫ t,β t)=1 := by
    rw [circlePeriodize_integral_short hBc hBs]
    exact (integral_sub_right_eq_self b a).trans hb1
  have he (y : TransverseProduct) :
      A.indicator (fun y : TransverseProduct ↦ (real_periodic_deriv hp).lift (y j)) y=2*β (y j) := by
    let t : ℝ := ((AddCircle.equivIco (1 : ℝ) (d-1/2)) (y j) : ℝ)
    have ht0 := ((AddCircle.equivIco (1 : ℝ) (d-1/2)) (y j)).property
    have ht : t∈Icc (d-1/2) (d+1/2) := by
      change d-1/2≤t ∧ t<d-1/2+1 at ht0
      constructor <;> linarith [ht0.1,ht0.2]
    have hty : (t : AxisCircle)=y j := (AddCircle.equivIco (1 : ℝ) (d-1/2)).symm_apply_apply _
    have hBt : β (y j)=b (t-a) := by
      rw [←hty]
      exact (circlePeriodize_eventuallyEq hBc hBs ht).eq_of_nhds
    rw [hBt]
    by_cases hy : y∈A
    · have hc0 : b (t-c)=0 := by
        by_contra hnc
        exact hout t hnc y hty.symm hy
      rw [indicator_of_mem hy,←hty]
      change deriv ψ t=2*b (t-a)
      rw [hd t ht,hc0,sub_zero]
    · have ha0 : b (t-a)=0 := by
        by_contra hna
        exact hy (hin t hna y hty.symm)
      simp [hy,ha0]
  have hflux : (∫ y in A,(real_periodic_deriv hp).lift (y j))=2 := by
    rw [←integral_indicator hA,funext he,integral_const_mul]
    have hmp : MeasurePreserving (Function.eval j) (volume : Measure TransverseProduct)
        (volume : Measure AxisCircle) := measurePreserving_eval (fun _ : Fin 2 ↦ (volume : Measure AxisCircle)) j
    have hem := integral_map (μ := (volume : Measure TransverseProduct)) hmp.measurable.aemeasurable
      (show AEStronglyMeasurable β (Measure.map (fun y : TransverseProduct ↦ y j) volume) from
        hβ.aestronglyMeasurable)
    rw [hmp.map_eq] at hem
    rw [←hem,hβi,mul_one]
  have hh := planarTorusPerimeter_ge_axial_flux A j hψ hp hbψ
  simpa only [hflux,ENNReal.ofReal_ofNat] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_open_fiber_collar {A : Set TransverseProduct} (hA : IsOpen A)
    (j : Fin 2) (a : ℝ)
    (ha : ∀ y : TransverseProduct,y j=(a : AxisCircle) → y∈A) :
    ∃ ε : ℝ,0<ε ∧ ∀ t : ℝ,|t-a|<ε → ∀ y : TransverseProduct,y j=(t : AxisCircle) → y∈A := by
  have hc : IsCompact Aᶜ := hA.isClosed_compl.isCompact
  have hj : Continuous (Function.eval j : TransverseProduct → AxisCircle) := continuous_apply j
  have ho : IsOpen ((Function.eval j '' Aᶜ)ᶜ : Set AxisCircle) := (hc.image hj).isClosed.isOpen_compl
  have hm : (a : AxisCircle)∈((Function.eval j '' Aᶜ)ᶜ : Set AxisCircle) := by
    rintro ⟨y,hy,he⟩
    exact hy (ha y he)
  have hpre := ho.preimage (AddCircle.continuous_mk' (1 : ℝ))
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hpre a hm
  refine ⟨ε,hε,fun t ht y hy ↦ ?_⟩
  have hh := hball (show t∈Metric.ball a ε from by simpa only [Metric.mem_ball,Real.dist_eq] using ht)
  by_contra hny
  exact hh ⟨y,hny,hy⟩

theorem planarTorusPerimeter_ge_two_of_open_fibers
    {A : Set TransverseProduct} (hA : IsOpen A) (j : Fin 2) {a c : ℝ}
    (hac : a≤c) (hshort : c-a<1)
    (hin : ∀ y : TransverseProduct,y j=(a : AxisCircle) → y∈A)
    (hout : ∀ y : TransverseProduct,y j=(c : AxisCircle) → y∉closure A) :
    (2 : ℝ≥0∞)≤planarTorusPerimeter A := by
  obtain ⟨ε,hε,hεA⟩ := planar_open_fiber_collar hA j a hin
  obtain ⟨δ,hδ,hδA⟩ := planar_open_fiber_collar isClosed_closure.isOpen_compl j c hout
  let r : ℝ := min (min ε δ) (1-(c-a))/4
  have hr : 0<r := by dsimp [r]; positivity
  have hrε : r<ε := by
    have hh := (min_le_left (min ε δ) (1-(c-a))).trans (min_le_left ε δ)
    dsimp only [r]
    linarith
  have hrδ : r<δ := by
    have hh := (min_le_left (min ε δ) (1-(c-a))).trans (min_le_right ε δ)
    dsimp only [r]
    linarith
  have hrc : c-a+2*r<1 := by
    have hh := min_le_right (min ε δ) (1-(c-a))
    dsimp only [r]
    linarith
  let b : ContDiffBump (0 : ℝ) := ⟨r/2,r,half_pos hr,by linarith⟩
  apply planarTorusPerimeter_ge_two_of_bump_strips hA.measurableSet j b.contDiff_normed
    b.integrable_normed (fun t ↦ b.nonneg_normed t) b.integral_normed (r := r) (a := a) (c := c)
  · rw [b.tsupport_normed_eq,Real.closedBall_eq_Icc]
    simp only [sub_eq_add_neg,zero_add]
    exact Subset.rfl
  · exact hac
  · exact hrc
  · intro t ht y hy
    have hs : t-a∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]
      exact ht
    have hab : |t-a|<r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hs
    exact hεA t (hab.trans hrε) y hy
  · intro t ht y hy hya
    have hs : t-c∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]
      exact ht
    have hab : |t-c|<r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hs
    exact hδA t (hab.trans hrδ) y hy (subset_closure hya)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSectionCorner (b : Fin 3 → Bool) (i : Fin 3) (t : ℝ) (n : Fin 2 → Bool) : Cover :=
  WithLp.toLp 2 (i.insertNth t (fun j ↦ octantHeight b (i.succAbove j) (if n j then 1 else 0)))

@[simp] lemma axialSectionCorner_same (b : Fin 3 → Bool) (i : Fin 3) (t : ℝ) (n : Fin 2 → Bool) :
    axialSectionCorner b i t n i=t := by simp [axialSectionCorner]
@[simp] lemma axialSectionCorner_other (b : Fin 3 → Bool) (i : Fin 3) (t : ℝ) (n : Fin 2 → Bool) (j : Fin 2) :
    axialSectionCorner b i t n (i.succAbove j)=octantHeight b (i.succAbove j) (if n j then 1 else 0) := by
  simp [axialSectionCorner]

lemma axialSectionCorner_mem (b : Fin 3 → Bool) (i : Fin 3) {t : ℝ}
    (ht : t∈Icc (1/2 : ℝ) 1) (n : Fin 2 → Bool) : axialSectionCorner b i t n∈closedUpperOctant := by
  intro k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨j,rfl⟩
  · simpa using ht
  · rw [axialSectionCorner_other]
    exact octantHeight_mem b _ (by split_ifs <;> constructor <;> norm_num)

lemma octantHeight_zero_le (b : Fin 3 → Bool) (k : Fin 3) {s : ℝ} (hs : s∈Icc (1/2 : ℝ) 1) :
    (if b k then (octantHeight b k 0 ≤ s) else (s ≤ octantHeight b k 0)) := by
  unfold octantHeight
  cases b k <;> simp_all only [Bool.false_eq_true,ite_false,ite_true,add_zero,zero_div,sub_zero] <;> first | exact hs.1 | exact hs.2

lemma octantHeight_le_one (b : Fin 3 → Bool) (k : Fin 3) {s : ℝ} (hs : s∈Icc (1/2 : ℝ) 1) :
    (if b k then (s ≤ octantHeight b k 1) else (octantHeight b k 1 ≤ s)) := by
  unfold octantHeight
  cases b k <;> simp_all only [Bool.false_eq_true,ite_false,ite_true] <;> linarith [hs.1,hs.2]

lemma torusAxialSplit_symm_continuous (i : Fin 3) :
    Continuous (torusAxialSplit i).symm := by
  change Continuous (fun p : AxisCircle × TransverseProduct ↦ WithLp.toLp 2 (i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) p.1 p.2))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  exact (Fin.forall_iff_succAbove (P := fun j : Fin 3 ↦ Continuous
    (fun p : AxisCircle × TransverseProduct ↦ (i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) p.1 p.2) j)) i).mpr
    ⟨by simp only [Fin.insertNth_apply_same]; exact continuous_fst,
      fun k ↦ by simp only [Fin.insertNth_apply_succAbove]; exact (continuous_apply k).comp continuous_snd⟩ j

lemma axialSlice_isOpen {O : Set Torus} (hO : IsOpen O) (i : Fin 3) (t : AxisCircle) :
    IsOpen (axialSlice O i t) :=
  hO.preimage ((torusAxialSplit_symm_continuous i).comp (continuous_const.prodMk continuous_id))

lemma axialSlice_closure_subset (O : Set Torus) (i : Fin 3) (t : AxisCircle) :
    closure (axialSlice O i t)⊆axialSlice (closure O) i t := by
  apply closure_minimal
  · exact preimage_mono subset_closure
  · exact isClosed_closure.preimage
      ((torusAxialSplit_symm_continuous i).comp (continuous_const.prodMk continuous_id))

lemma upperFold_closure_mem {O : Set Torus}
    (hR : ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈O ↔ z∈O)
    {z : Torus} (hz : z∈closure O) : quotientMap (upperFold z)∈closure O := by
  apply (closure_minimal (s := O)
    (t := (fun z : Torus ↦ quotientMap (upperFold z)) ⁻¹' closure O)
    (fun z hz ↦ subset_closure ((upperFold_phase hR z).mpr hz))
    (isClosed_closure.preimage (continuous_quotientMap.comp upperFold_continuous))) hz

lemma upperFold_slice_fixed (b : Fin 3 → Bool) (i : Fin 3) (j : Fin 2)
    (t : AxisCircle) (y : TransverseProduct) {s : ℝ} (hs : s∈Icc 0 1)
    (hy : y j=(octantHeight b (i.succAbove j) s : AxisCircle)) :
    upperFold ((torusAxialSplit i).symm (t,y)) (i.succAbove j)=octantHeight b (i.succAbove j) s := by
  rw [upperFold_slice_succAbove,hy,circle_norm_upper (octantHeight_mem b _ hs)]
  ring

lemma isMinimizerAt_section_full_fiber {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (j : Fin 2) {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1)
    (hv : quotientMap (axialSectionCorner b i t (fun k ↦ if k=j then false else true))∈openRepresentative E) :
    ∀ y : TransverseProduct,y j=(octantHeight b (i.succAbove j) 0 : AxisCircle) →
      y∈axialSlice (openRepresentative E) i (t : AxisCircle) := by
  intro y hy
  let z : Torus := (torusAxialSplit i).symm ((t : AxisCircle),y)
  apply (upperFold_phase (reflection_invariant_openRepresentative hmin.1.1 hR) z).mp
  apply isMinimizerAt_closed_octant_order hV hmin hR hd (upperFold_mem z)
    (axialSectionCorner_mem b i ht _) _ hv
  intro k
  rcases Fin.eq_self_or_eq_succAbove i k with hki|⟨k,rfl⟩
  · subst k
    rw [axialSectionCorner_same,upperFold_slice_same i ht]
    unfold OrientedCoordinateLE at *
    split_ifs <;> exact le_rfl
  · rw [axialSectionCorner_other]
    by_cases hkj : k=j
    · subst k
      simp only [ite_true,Bool.false_eq_true,ite_false]
      rw [upperFold_slice_fixed b i j (t : AxisCircle) y (by constructor <;> norm_num) hy]
      split_ifs <;> exact le_rfl
    · rw [ite_eq_right hkj]
      exact octantHeight_le_one b _ (upperFold_mem z _)

lemma isMinimizerAt_section_empty_closed_fiber {V : ℝ} (_hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (j : Fin 2) {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1)
    (hv : quotientMap (axialSectionCorner b i t (fun k ↦ if k=j then true else false))∉closure (openRepresentative E)) :
    ∀ y : TransverseProduct,y j=(octantHeight b (i.succAbove j) 1 : AxisCircle) →
      y∉closure (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  intro y hy hya
  let z : Torus := (torusAxialSplit i).symm ((t : AxisCircle),y)
  have hz : z∈closure (openRepresentative E) := axialSlice_closure_subset _ i _ hya
  have hzf := upperFold_closure_mem (reflection_invariant_openRepresentative hmin.1.1 hR) hz
  apply hv
  apply octant_downset_closure (isOpen_openRepresentative E)
    (reflection_invariant_openRepresentative hmin.1.1 hR) hd (axialSectionCorner_mem b i ht _)
    (upperFold_mem z) _ hzf
  intro k
  rcases Fin.eq_self_or_eq_succAbove i k with hki|⟨k,rfl⟩
  · subst k
    rw [axialSectionCorner_same,upperFold_slice_same i ht]
    split_ifs <;> exact le_rfl
  · rw [axialSectionCorner_other]
    by_cases hkj : k=j
    · subst k
      simp only [ite_true]
      rw [upperFold_slice_fixed b i j (t : AxisCircle) y (by constructor <;> norm_num) hy]
      split_ifs <;> exact le_rfl
    · rw [ite_eq_right hkj]
      exact octantHeight_zero_le b _ (upperFold_mem z _)

theorem isMinimizerAt_section_strip_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (j : Fin 2) {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1)
    (hin : quotientMap (axialSectionCorner b i t (fun k ↦ if k=j then false else true))∈openRepresentative E)
    (hout : quotientMap (axialSectionCorner b i t (fun k ↦ if k=j then true else false))∉closure (openRepresentative E)) :
    (2 : ℝ≥0∞)≤planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  let a : ℝ := if b (i.succAbove j) then 1/2 else 0
  have hzero : (a : AxisCircle)=(octantHeight b (i.succAbove j) 0 : AxisCircle) := by
    dsimp only [a,octantHeight]
    cases b (i.succAbove j) <;> simp [AddCircle.coe_period]
  have hone : ((a+1/2 : ℝ) : AxisCircle)=(octantHeight b (i.succAbove j) 1 : AxisCircle) := by
    apply congrArg (fun x : ℝ ↦ (x : AxisCircle))
    dsimp only [a,octantHeight]
    cases b (i.succAbove j) <;> norm_num
  apply planarTorusPerimeter_ge_two_of_open_fibers (axialSlice_isOpen (isOpen_openRepresentative E) i _) j
    (a := a) (c := a+1/2) (by linarith) (by linarith)
  · intro y hy
    apply isMinimizerAt_section_full_fiber hV hmin hR hd i j ht hin y
    exact hy.trans hzero
  · intro y hy
    apply isMinimizerAt_section_empty_closed_fiber hV hmin hR hd i j ht hout y
    exact hy.trans hone

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarProductField (σ a b : ℝ → ℝ) (y : Plane) : Plane :=
  (σ (y 0)*a (y 1)) • EuclideanSpace.single 0 1 +
    b (y 1) • EuclideanSpace.single 1 1

lemma planarProductField_admissible {σ a b : ℝ → ℝ}
    (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (pσ : Function.Periodic σ 1) (pa : Function.Periodic a 1) (pb : Function.Periodic b 1)
    (hσb : ∀ x,|σ x|≤1) (hab : ∀ y,(a y)^2+(b y)^2≤1) :
    PlanarAdmissibleField (planarProductField σ a b) := by
  have hx := (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).contDiff (n := (⊤ : ℕ∞))
  have hy := (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).contDiff (n := (⊤ : ℕ∞))
  refine ⟨((hσ.comp hx).mul (ha.comp hy)).smul contDiff_const |>.add
    ((hb.comp hy).smul contDiff_const),?_,?_⟩
  · intro n y
    unfold planarProductField
    simp only [PiLp.add_apply]
    have hs := pσ.int_mul (n 0) (y 0)
    have ha := pa.int_mul (n 1) (y 1)
    have hb := pb.int_mul (n 1) (y 1)
    simp only [mul_one] at hs ha hb
    rw [hs,ha,hb]
  · intro y
    have hs : (σ (y 0))^2≤1 := by nlinarith [sq_abs (σ (y 0)),hσb (y 0),abs_nonneg (σ (y 0))]
    have hn : ‖planarProductField σ a b y‖^2≤1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [Fin.sum_univ_two,planarProductField,PiLp.add_apply,PiLp.smul_apply,
        PiLp.single_apply,Fin.isValue,ite_true,smul_eq_mul,
        mul_one,Fin.reduceEq,ite_false,mul_zero,add_zero,zero_add,Real.norm_eq_abs,sq_abs]
      nlinarith [hab (y 1),mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (a (y 1)))]
    nlinarith [norm_nonneg (planarProductField σ a b y)]

lemma planeDivergence_planarProductField {σ a b : ℝ → ℝ}
    (hσ : Differentiable ℝ σ) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (y : Plane) : planeDivergence (planarProductField σ a b) y=
      deriv σ (y 0)*a (y 1)+deriv b (y 1) := by
  have hx := (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := y)
  have hy := (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := y)
  have hd := (((hσ (y 0)).hasDerivAt.comp_hasFDerivAt y hx).mul
    ((ha (y 1)).hasDerivAt.comp_hasFDerivAt y hy)).smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
  have he := ((hb (y 1)).hasDerivAt.comp_hasFDerivAt y hy).smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
  have hf := hd.add he
  change HasFDerivAt (planarProductField σ a b) _ y at hf
  rw [planeDivergence,hf.fderiv]
  simp [ContinuousLinearMap.smulRight_apply,mul_comm]

theorem planarTorusPerimeter_ge_product_flux (A : Set TransverseProduct)
    {σ a b : ℝ → ℝ}
    (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (pσ : Function.Periodic σ 1) (pa : Function.Periodic a 1) (pb : Function.Periodic b 1)
    (hσb : ∀ x,|σ x|≤1) (hab : ∀ y,(a y)^2+(b y)^2≤1) :
    ENNReal.ofReal (∫ y in A,(real_periodic_deriv pσ).lift (y 0)*pa.lift (y 1)+
      (real_periodic_deriv pb).lift (y 1))≤planarTorusPerimeter A := by
  have he (y : TransverseProduct) :
      planeDivergence (planarProductField σ a b) (planarRepresentative y)=
        (real_periodic_deriv pσ).lift (y 0)*pa.lift (y 1)+
          (real_periodic_deriv pb).lift (y 1) := by
    rw [planeDivergence_planarProductField (hσ.differentiable (by simp))
      (ha.differentiable (by simp)) (hb.differentiable (by simp))]
    have e0 := (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (y 0)
    have e1 := (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (y 1)
    change (((AddCircle.equivIco (1 : ℝ) 0) (y 0) : ℝ) : AxisCircle)=y 0 at e0
    change (((AddCircle.equivIco (1 : ℝ) 0) (y 1) : ℝ) : AxisCircle)=y 1 at e1
    conv_rhs => rw [←e0,←e1]
    rfl
  rw [←show (∫ y in A,planeDivergence (planarProductField σ a b) (planarRepresentative y))=
      ∫ y in A,(real_periodic_deriv pσ).lift (y 0)*pa.lift (y 1)+
        (real_periodic_deriv pb).lift (y 1) by apply integral_congr_ae; exact Filter.Eventually.of_forall he]
  exact le_iSup_of_le (planarProductField σ a b)
    (le_iSup_of_le (planarProductField_admissible hσ ha hb pσ pa pb hσb hab) le_rfl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma transverse_integral_mul (f g : AxisCircle → ℝ) :
    (∫ y : TransverseProduct,f (y 0)*g (y 1))=(∫ t,f t)*(∫ t,g t) := by
  simpa only [Fin.prod_univ_two,Fin.isValue,Fin.reduceFinMk,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons] using
    integral_fintype_prod_volume_eq_prod (E := fun _ : Fin 2 ↦ AxisCircle) ![f,g]

theorem planarTorusPerimeter_ge_weighted_bump_strips
    {A : Set TransverseProduct} (hA : MeasurableSet A)
    {T : Set AxisCircle} (hT : MeasurableSet T)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (pu : Function.Periodic u 1) (pv : Function.Periodic v 1)
    (hu0 : ∀ y,0≤u y) (huv : ∀ y,(u y)^2+(v y)^2≤1)
    {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbi : Integrable b volume)
    (hb0 : ∀ t,0≤b t) (hb1 : ∫ t,b t=1)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a≤c)
    (hshort : c-a+2*r<1)
    (hin : ∀ t : ℝ,b (t-a)≠0 → ∀ y : TransverseProduct,y 0=(t : AxisCircle) → y 1∈T → y∈A)
    (hout : ∀ t : ℝ,b (t-c)≠0 → ∀ y : TransverseProduct,y 0=(t : AxisCircle) → y∉A)
    {k : ℝ} (hk : ∀ y∈A,(real_periodic_deriv pv).lift (y 1)=k) :
    ENNReal.ofReal (k*volume.real A+2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
  let H := intervalSmoothHat b a c
  let d := (a+c)/2
  have hHs : tsupport H ⊆ Ioo (d-1/2) (d+1/2) := by
    apply (intervalSmoothHat_support hb.continuous hs hac).trans
    intro x hx
    dsimp only [d]
    constructor <;> linarith [hx.1,hx.2]
  have hHc : HasCompactSupport H :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport H)
      (intervalSmoothHat_support hb.continuous hs hac)
  let B : ℝ → ℝ := fun t ↦ b (t-a)
  have hBs : tsupport B ⊆ Ioo (d-1/2) (d+1/2) := by
    intro t ht
    have hh := hs (tsupport_comp_subset_preimage b (continuous_id.sub continuous_const) ht)
    change -r≤t-a ∧ t-a≤r at hh
    dsimp only [d]
    constructor <;> linarith [hh.1,hh.2]
  have hBc : HasCompactSupport B :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport B)
      (fun _ ht ↦ ⟨(hBs ht).1.le,(hBs ht).2.le⟩)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hb.comp (contDiff_id.sub contDiff_const)
  let ψ : ℝ → ℝ := fun t ↦ 2*circlePeriodize H t-1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (contDiff_const.mul (circlePeriodize_contDiff (intervalSmoothHat_contDiff hb a c) hHc)).sub contDiff_const
  have hp : Function.Periodic ψ 1 := fun t ↦ by
    dsimp only [ψ]
    rw [circlePeriodize_periodic H t]
  have hbψ (t : ℝ) : |ψ t|≤1 := by
    have hh := circlePeriodize_unit_bounds hHs (fun t ↦
      ⟨intervalSmoothHat_nonneg hb.continuous hb0 hac t,
        intervalSmoothHat_le_one hb.continuous hbi hb0 hb1 hac t⟩) t
    apply abs_le.mpr
    dsimp only [ψ]
    constructor <;> linarith [hh.1,hh.2]
  have hd (t : ℝ) (ht : t∈Icc (d-1/2) (d+1/2)) : deriv ψ t=2*(b (t-a)-b (t-c)) := by
    have he := circlePeriodize_eventuallyEq hHc hHs ht
    dsimp only [ψ]
    rw [deriv_sub_const,deriv_const_mul 2
      ((circlePeriodize_contDiff (intervalSmoothHat_contDiff hb a c) hHc).differentiable (by simp) t),
      he.deriv_eq,(intervalSmoothHat_hasDerivAt hb.continuous a c t).deriv]
  let β : AxisCircle → ℝ := (circlePeriodize_periodic B).lift
  have hβ : Continuous β := continuous_periodic_lift _ (circlePeriodize_contDiff hB hBc).continuous
  have hβi : (∫ t,β t)=1 := by
    rw [circlePeriodize_integral_short hBc hBs]
    exact (integral_sub_right_eq_self b a).trans hb1
  have huC : Continuous (pu.lift : AxisCircle → ℝ) := continuous_periodic_lift _ hu.continuous
  have hvC : Continuous ((real_periodic_deriv pv).lift : AxisCircle → ℝ) :=
    continuous_periodic_lift _ (hv.continuous_deriv (by simp))
  have hσC : Continuous ((real_periodic_deriv hp).lift : AxisCircle → ℝ) :=
    continuous_periodic_lift _ (hψ.continuous_deriv (by simp))
  have huL (t : AxisCircle) : 0≤pu.lift t := by
    induction t using Quotient.inductionOn with | h t => exact hu0 t
  have he (y : TransverseProduct) :
      2*β (y 0)*(T.indicator pu.lift (y 1))≤
        A.indicator (fun y : TransverseProduct ↦ (real_periodic_deriv hp).lift (y 0)*pu.lift (y 1)) y := by
    let t : ℝ := ((AddCircle.equivIco (1 : ℝ) (d-1/2)) (y 0) : ℝ)
    have ht0 := ((AddCircle.equivIco (1 : ℝ) (d-1/2)) (y 0)).property
    have ht : t∈Icc (d-1/2) (d+1/2) := by
      change d-1/2≤t ∧ t<d-1/2+1 at ht0
      constructor <;> linarith [ht0.1,ht0.2]
    have hty : (t : AxisCircle)=y 0 := (AddCircle.equivIco (1 : ℝ) (d-1/2)).symm_apply_apply _
    have hBt : β (y 0)=b (t-a) := by
      rw [←hty]
      exact (circlePeriodize_eventuallyEq hBc hBs ht).eq_of_nhds
    rw [hBt]
    by_cases hy : y∈A
    · have hc0 : b (t-c)=0 := by
        by_contra hnc
        exact hout t hnc y hty.symm hy
      rw [indicator_of_mem hy]
      have hd' : (real_periodic_deriv hp).lift (y 0)=2*b (t-a) := by
        rw [←hty]
        change deriv ψ t=2*b (t-a)
        rw [hd t ht,hc0,sub_zero]
      rw [hd']
      by_cases hyT : y 1∈T
      · rw [indicator_of_mem hyT]
      · rw [indicator_of_notMem hyT,mul_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) (hb0 _)) (huL _)
    · rw [indicator_of_notMem hy]
      by_cases hyT : y 1∈T
      · have ha0 : b (t-a)=0 := by
          by_contra hna
          exact hy (hin t hna y hty.symm hyT)
        rw [ha0,mul_zero,zero_mul]
      · rw [indicator_of_notMem hyT,mul_zero]
  have hiR : Integrable (fun y : TransverseProduct ↦
      (real_periodic_deriv hp).lift (y 0)*pu.lift (y 1)) :=
    ((hσC.comp (continuous_apply 0)).mul (huC.comp (continuous_apply 1))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiL : Integrable (fun y : TransverseProduct ↦ 2*β (y 0)*T.indicator pu.lift (y 1)) := by
    have hbase : Integrable (fun y : TransverseProduct ↦ 2*β (y 0)*pu.lift (y 1)) :=
      ((continuous_const.mul (hβ.comp (continuous_apply 0))).mul (huC.comp (continuous_apply 1))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    apply (hbase.indicator (hT.preimage (measurable_pi_apply 1))).congr
    filter_upwards [] with y
    by_cases hy : y 1∈T <;> simp [hy]
  have hle := integral_mono hiL (hiR.indicator hA) he
  have hlow : (∫ y : TransverseProduct,2*β (y 0)*T.indicator pu.lift (y 1))=
      2*(∫ t in T,pu.lift t) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul,transverse_integral_mul,hβi,one_mul,integral_indicator hT]
  rw [hlow,integral_indicator hA] at hle
  have hvI : Integrable (fun y : TransverseProduct ↦ (real_periodic_deriv pv).lift (y 1)) :=
    (hvC.comp (continuous_apply 1)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hflux := planarTorusPerimeter_ge_product_flux A hψ hu hv hp pu pv hbψ huv
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hflux
  rw [integral_add hiR.integrableOn hvI.integrableOn]
  have hev : (∫ y in A,(real_periodic_deriv pv).lift (y 1))=k*volume.real A := by
    calc
      _=∫ _ in A,k := setIntegral_congr_fun hA hk
      _=k*volume.real A := by simp [mul_comm,measureReal_def]
  rw [hev]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_open_partial_fiber_collar {A : Set TransverseProduct} (hA : IsOpen A)
    {T : Set AxisCircle} (hT : IsCompact T) (a : ℝ)
    (ha : ∀ y : TransverseProduct,y 0=(a : AxisCircle) →y 1∈T →y∈A) :
    ∃ ε : ℝ,0<ε ∧ ∀ t : ℝ,|t-a|<ε →∀ y : TransverseProduct,y 0=(t : AxisCircle) →y 1∈T →y∈A := by
  have h1 : Continuous (Function.eval (1 : Fin 2) : TransverseProduct → AxisCircle) := continuous_apply 1
  have h0 : Continuous (Function.eval (0 : Fin 2) : TransverseProduct → AxisCircle) := continuous_apply 0
  have hc : IsCompact (Aᶜ∩(Function.eval (1 : Fin 2)) ⁻¹' T) :=
    (hA.isClosed_compl.inter (hT.isClosed.preimage h1)).isCompact
  have ho : IsOpen ((Function.eval (0 : Fin 2) '' (Aᶜ∩(Function.eval (1 : Fin 2)) ⁻¹' T))ᶜ : Set AxisCircle) :=
    (hc.image h0).isClosed.isOpen_compl
  have hm : (a : AxisCircle)∈((Function.eval (0 : Fin 2) '' (Aᶜ∩(Function.eval (1 : Fin 2)) ⁻¹' T))ᶜ : Set AxisCircle) := by
    rintro ⟨y,⟨hy,hyT⟩,he⟩
    exact hy (ha y he hyT)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (ho.preimage (AddCircle.continuous_mk' (1 : ℝ))) a hm
  refine ⟨ε,hε,fun t ht y hy hyT ↦ ?_⟩
  have hh := hball (show t∈Metric.ball a ε from by simpa only [Metric.mem_ball,Real.dist_eq] using ht)
  by_contra hny
  exact hh ⟨y,⟨hny,hyT⟩,hy⟩

theorem planarTorusPerimeter_ge_corner_calibration
    {A : Set TransverseProduct} (hA : IsOpen A)
    {T : Set AxisCircle} (hT : IsCompact T)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (pu : Function.Periodic u 1) (pv : Function.Periodic v 1)
    (hu0 : ∀ y,0≤u y) (huv : ∀ y,(u y)^2+(v y)^2≤1)
    {a c : ℝ} (hac : a≤c) (hshort : c-a<1)
    (hin : ∀ y : TransverseProduct,y 0=(a : AxisCircle) →y 1∈T →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=(c : AxisCircle) →y∉closure A)
    {k : ℝ} (hk : ∀ y∈A,(real_periodic_deriv pv).lift (y 1)=k) :
    ENNReal.ofReal (k*volume.real A+2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
  obtain ⟨ε,hε,hεA⟩ := planar_open_partial_fiber_collar hA hT a hin
  obtain ⟨δ,hδ,hδA⟩ := planar_open_fiber_collar isClosed_closure.isOpen_compl 0 c hout
  let r : ℝ := min (min ε δ) (1-(c-a))/4
  have hr : 0<r := by dsimp [r]; positivity
  have hrε : r<ε := by
    have hh := (min_le_left (min ε δ) (1-(c-a))).trans (min_le_left ε δ)
    dsimp only [r]; linarith
  have hrδ : r<δ := by
    have hh := (min_le_left (min ε δ) (1-(c-a))).trans (min_le_right ε δ)
    dsimp only [r]; linarith
  have hrc : c-a+2*r<1 := by
    have hh := min_le_right (min ε δ) (1-(c-a))
    dsimp only [r]; linarith
  let b : ContDiffBump (0 : ℝ) := ⟨r/2,r,half_pos hr,by linarith⟩
  apply planarTorusPerimeter_ge_weighted_bump_strips hA.measurableSet hT.measurableSet
    hu hv pu pv hu0 huv b.contDiff_normed b.integrable_normed (fun t ↦ b.nonneg_normed t)
    b.integral_normed (r := r) (a := a) (c := c) _ hac hrc _ _ hk
  · rw [b.tsupport_normed_eq,Real.closedBall_eq_Icc]
    simp only [sub_eq_add_neg,zero_add]
    exact Subset.rfl
  · intro t ht y hy hyT
    have hs : t-a∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]; exact ht
    have hab : |t-a|<r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hs
    exact hεA t (hab.trans hrε) y hy hyT
  · intro t ht y hy hya
    have hs : t-c∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]; exact ht
    have hab : |t-c|<r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hs
    exact hδA t (hab.trans hrδ) y hy (subset_closure hya)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circlePeriodize_abs_lt_one {f : ℝ → ℝ} {a : ℝ}
    (hs : tsupport f ⊆ Ioo (a-1/2) (a+1/2))
    (hb : ∀ x,|f x|<1) (x : ℝ) : |circlePeriodize f x|<1 := by
  classical
  by_cases hn : ∃ n : ℤ,f (x+n)≠0
  · obtain ⟨n,hn⟩ := hn
    have huniq (m : ℤ) (hm : m≠n) : f (x+m)=0 := by
      by_contra hm'
      have h1 := hs (subset_tsupport f hn)
      have h2 := hs (subset_tsupport f hm')
      have hlo : (-1 : ℝ)<(m-n : ℤ) := by push_cast; linarith [h1.2,h2.1]
      have hhi : ((m-n : ℤ) : ℝ)<1 := by push_cast; linarith [h1.1,h2.2]
      have hlo' : (-1 : ℤ) < m-n := by exact_mod_cast hlo
      have hhi' : m-n<1 := by exact_mod_cast hhi
      omega
    rw [circlePeriodize,tsum_eq_single n huniq]
    exact hb _
  · push Not at hn
    simp only [circlePeriodize,hn,tsum_zero,abs_zero,zero_lt_one]

theorem exists_planar_affine_band_field {L q : ℝ} (hL : L∈Ioo 0 (1/2))
    (hq : q∈Ioo 0 1) :
    ∃ u v : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) u ∧ContDiff ℝ (⊤ : ℕ∞) v ∧
      Function.Periodic u 1 ∧Function.Periodic v 1 ∧
      (∀ y,0≤u y) ∧(∀ y,(u y)^2+(v y)^2=1) ∧
      (∀ y,|y|≤L →u y=Real.sqrt (1-(q/L*y)^2)) ∧
      (∀ y,|y|<L →deriv v y=q/L) := by
  have hLq : L<L/q := (lt_div_iff₀ hq.1).mpr (by nlinarith [hL.1,hq.2])
  obtain ⟨R,hLR,hR⟩ := exists_between (lt_min hL.2 hLq)
  have hRhalf : R<1/2 := hR.trans_le (min_le_left _ _)
  have hqR : (q/L)*R<1 := by
    have hh := (lt_div_iff₀ hq.1).mp (hR.trans_le (min_le_right _ _))
    rw [div_mul_eq_mul_div]
    apply (div_lt_one hL.1).mpr
    nlinarith
  let χ : ContDiffBump (0 : ℝ) := ⟨L,R,hL.1,hLR⟩
  let f : ℝ → ℝ := fun t ↦ (q/L*t)*χ t
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_const.mul contDiff_id).mul χ.contDiff
  have hfs : tsupport f ⊆ Ioo ((0 : ℝ)-1/2) (0+1/2) := by
    apply (tsupport_mul_subset_right (f := fun t ↦ q/L*t) (g := χ)).trans
    rw [χ.tsupport_eq,Real.closedBall_eq_Icc]
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f)
      (fun _ ht ↦ ⟨(hfs ht).1.le,(hfs ht).2.le⟩)
  have hfb (t : ℝ) : |f t|<1 := by
    by_cases hz : χ t=0
    · simp [f,hz]
    have ht : |t|<R := by
      have hh : t∈Metric.ball (0 : ℝ) R := by rwa [←χ.support_eq]
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hh
    have hqL : 0<q/L := div_pos hq.1 hL.1
    calc
      |f t|=(q/L)* |t| *χ t := by simp only [f,abs_mul,abs_of_pos hqL,abs_of_nonneg χ.nonneg]
      _≤(q/L)* |t| := mul_le_of_le_one_right (mul_nonneg hqL.le (abs_nonneg _)) χ.le_one
      _<(q/L)*R := mul_lt_mul_of_pos_left ht hqL
      _<1 := hqR
  let v := circlePeriodize f
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := circlePeriodize_contDiff hf hfc
  have hpv : Function.Periodic v 1 := circlePeriodize_periodic f
  have hvb (t : ℝ) : |v t|<1 := circlePeriodize_abs_lt_one hfs hfb t
  have hpos (t : ℝ) : 0<1-(v t)^2 := by
    nlinarith [hvb t,abs_nonneg (v t),sq_abs (v t)]
  let u : ℝ → ℝ := fun t ↦ Real.sqrt (1-(v t)^2)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := (contDiff_const.sub (hv.pow 2)).sqrt (fun t ↦ (hpos t).ne')
  have hpu : Function.Periodic u 1 := fun t ↦ by dsimp only [u]; rw [hpv t]
  refine ⟨u,v,hu,hv,hpu,hpv,fun t ↦ Real.sqrt_nonneg _,?_,?_,?_⟩
  · intro t
    dsimp only [u]
    rw [Real.sq_sqrt (hpos t).le]
    ring
  · intro t ht
    have htc : t∈Icc ((0 : ℝ)-1/2) (0+1/2) := by
      obtain ⟨ht0,ht1⟩ := abs_le.mp ht
      constructor <;> linarith
    have hχ : χ t=1 := χ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using ht)
    dsimp only [u,v]
    rw [(circlePeriodize_eventuallyEq hfc hfs htc).eq_of_nhds]
    simp only [f,hχ,mul_one]
  · intro t ht
    have htc : t∈Icc ((0 : ℝ)-1/2) (0+1/2) := by
      obtain ⟨ht0,ht1⟩ := abs_lt.mp ht
      constructor <;> linarith
    have hχ := χ.eventuallyEq_one_of_mem_ball (show t∈Metric.ball (0 : ℝ) L from by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
    have he : f=ᶠ[𝓝 t](fun t : ℝ ↦ q/L*t) := by
      filter_upwards [hχ] with x hx
      simp only [f,hx,Pi.one_apply,mul_one]
    change deriv (circlePeriodize f) t=q/L
    rw [(circlePeriodize_eventuallyEq hfc hfs htc).deriv_eq,he.deriv_eq]
    simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def closedCentralArc (K : ℝ) : Set AxisCircle := (fun t : ℝ ↦ (t : AxisCircle)) '' Icc (-K) K

lemma closedCentralArc_isCompact (K : ℝ) : IsCompact (closedCentralArc K) :=
  isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))

end CubicTorus
end
end
end

end OAI
