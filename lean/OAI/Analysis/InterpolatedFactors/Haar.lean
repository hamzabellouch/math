import OAI.Analysis.InterpolatedFactors.CornerRange

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15

open MeasureTheory Set CompactlySupported
open scoped ENNReal
namespace FreeGroupFactorMain.CyclicSpectral

section
variable {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
abbrev Space := spectrum ℝ A

instance compactSpace : CompactSpace (Space A) := isCompact_iff_compactSpace.mp (spectrum.isCompact A)

def functional : C_c(Space A,ℝ) →ₚ[ℝ] ℝ where
  toFun f := (inner ℂ ξ (cfcHom hA f.toContinuousMap ξ)).re
  map_add' f g := by
    change (inner ℂ ξ (cfcHom hA (f.toContinuousMap+g.toContinuousMap) ξ)).re=_
    rw [map_add,add_apply,inner_add_right,Complex.add_re]
  map_smul' c f := by
    change (inner ℂ ξ (cfcHom hA (c • f.toContinuousMap) ξ)).re=_
    rw [map_smul,_root_.smul_apply]
    change inner ℝ ξ (c • cfcHom hA f.toContinuousMap ξ)=c * inner ℝ ξ (cfcHom hA f.toContinuousMap ξ)
    exact real_inner_smul_right _ _ _
  monotone' f g hfg := by
    have hn : 0 ≤ cfcHom hA (g.toContinuousMap-f.toContinuousMap) :=
      (cfcHom_nonneg_iff hA).mpr (sub_nonneg.mpr hfg)
    have hi := (ContinuousLinearMap.nonneg_iff_isPositive.mp hn).re_inner_nonneg_right ξ
    rw [map_sub,sub_apply,inner_sub_right] at hi
    change 0 ≤ (inner ℂ ξ (cfcHom hA g.toContinuousMap ξ)).re-
      (inner ℂ ξ (cfcHom hA f.toContinuousMap ξ)).re at hi
    exact sub_nonneg.mp hi

def measure : Measure (Space A) := RealRMK.rieszMeasure (functional A hA ξ)

instance measure_regular : (measure A hA ξ).Regular := inferInstanceAs
  (RealRMK.rieszMeasure (functional A hA ξ)).Regular

instance measure_finite : IsFiniteMeasure (measure A hA ξ) := inferInstance

 theorem integral_continuous (f : C(Space A,ℝ)) :
    ∫ x, f x ∂measure A hA ξ=(inner ℂ ξ (cfcHom hA f ξ)).re := by
  exact RealRMK.integral_rieszMeasure (functional A hA ξ)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)

 theorem measure_univ : measure A hA ξ univ=ENNReal.ofReal (‖ξ‖^2) := by
  have hi := integral_continuous A hA ξ (1 : C(Space A,ℝ))
  simp only [ContinuousMap.one_apply,integral_const,map_one,one_apply_eq_self] at hi
  have hh : (measure A hA ξ).real univ=‖ξ‖^2 := by
    simpa only [smul_eq_mul,mul_one] using hi.trans (norm_sq_eq_re_inner (𝕜 := ℂ) ξ).symm
  rw [← hh,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]

 theorem integral_sq (f : C(Space A,ℝ)) :
    ∫ x, (f x)^2 ∂measure A hA ξ=‖cfcHom hA f ξ‖^2 := by
  have hi := integral_continuous A hA ξ (f*f)
  have hs : IsSelfAdjoint (cfcHom hA f) := cfcHom_predicate hA f
  calc
    _ = (inner ℂ ξ (cfcHom hA (f*f) ξ)).re := by
      simpa only [ContinuousMap.mul_apply,pow_two] using hi
    _ = (inner ℂ (cfcHom hA f ξ) (cfcHom hA f ξ)).re := by
      rw [map_mul,mul_apply_eq_comp]
      have he : inner ℂ ξ (cfcHom hA f (cfcHom hA f ξ))=
          inner ℂ (cfcHom hA f ξ) (cfcHom hA f ξ) := by
        calc
          _ = inner ℂ ξ (star (cfcHom hA f) (cfcHom hA f ξ)) := by rw [hs.star_eq]
          _ = _ := by rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      exact congrArg Complex.re he
    _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

 theorem probability (hξ : ‖ξ‖=1) : IsProbabilityMeasure (measure A hA ξ) := by
  constructor
  rw [measure_univ,hξ,one_pow,ENNReal.ofReal_one]

end
section
open MeasureTheory
variable {H : Type u_2} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def complexHom : C(Space A,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  let e := SpectrumRestricts.homeomorph (f := ⟨Complex.re,Complex.continuous_re⟩) hA.spectrumRestricts
  (cfcHom hA.isStarNormal).comp (ContinuousMap.compStarAlgHom' ℂ ℂ ⟨e,e.continuous⟩)

def complexLift (f : C(Space A,ℝ)) : C(Space A,ℂ) :=
  ⟨fun x => (f x:ℂ), Complex.continuous_ofReal.comp f.continuous⟩

 theorem complexHom_real (f : C(Space A,ℝ)) :
    complexHom A hA (complexLift A f)=cfcHom hA f := by
  rw [SpectrumRestricts.cfcHom_eq_restrict ⟨Complex.re,Complex.continuous_re⟩ hA hA.isStarNormal hA.spectrumRestricts]
  rfl

 theorem real_inner_im (f : C(Space A,ℝ)) :
    (inner ℂ ξ (cfcHom hA f ξ)).im=0 := by
  have hs := cfcHom_predicate hA f
  have he : star (inner ℂ ξ (cfcHom hA f ξ))=inner ℂ ξ (cfcHom hA f ξ) := by
    change (starRingEnd ℂ) (inner ℂ ξ (cfcHom hA f ξ))=_
    rw [inner_conj_symm]
    calc
      _ = inner ℂ ξ (star (cfcHom hA f) ξ) := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = _ := by rw [hs.star_eq]
  have hh := congrArg Complex.im he
  simp only [Complex.star_def,Complex.conj_im] at hh
  linarith

 theorem integral_complexLift (f : C(Space A,ℝ)) :
    ∫ x, complexLift A f x ∂measure A hA ξ=inner ℂ ξ (complexHom A hA (complexLift A f) ξ) := by
  rw [complexHom_real]
  change (∫ x, (f x:ℂ) ∂measure A hA ξ)=_
  rw [integral_complex_ofReal,integral_continuous]
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im,real_inner_im]

 theorem integral_complex (f : C(Space A,ℂ)) :
    ∫ x, f x ∂measure A hA ξ=inner ℂ ξ (complexHom A hA f ξ) := by
  let fr : C(Space A,ℝ) := ⟨fun x => (f x).re,Complex.continuous_re.comp f.continuous⟩
  let fi : C(Space A,ℝ) := ⟨fun x => (f x).im,Complex.continuous_im.comp f.continuous⟩
  have hf : f=complexLift A fr+Complex.I • complexLift A fi := by
    ext x
    change f x=(f x).re+(Complex.I:ℂ)*(f x).im
    simpa only [mul_comm Complex.I] using (Complex.re_add_im (f x)).symm
  rw [hf,map_add,map_smul,add_apply,_root_.smul_apply,inner_add_right,inner_smul_right]
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply]
  have hir : Integrable (fun x => complexLift A fr x) (measure A hA ξ) :=
    (complexLift A fr).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hii : Integrable (fun x => Complex.I • complexLift A fi x) (measure A hA ξ) :=
    (((complexLift A fi).continuous.const_smul Complex.I).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [integral_add hir hii,integral_smul,integral_complexLift,integral_complexLift]
  rfl

end
section
variable {H : Type u_3} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
 theorem complexHom_mem (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : IsClosed (S : Set (H →L[ℂ] H))) (hAS : A ∈ S) (f : C(Space A,ℂ)) :
    complexHom A hA f ∈ S := by
  apply StarSubalgebra.topologicalClosure_minimal (t := S) (by simpa) hS
    (cfcHom_mem_elemental hA.isStarNormal _)
end
open MeasureTheory
variable {H : Type u_4} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def complexEvaluate : C(Space A,ℂ) →ₗ[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H ξ).toLinearMap.comp (complexHom A hA).toAlgHom.toLinearMap

 theorem complexEvaluate_inner (f g : C(Space A,ℂ)) :
    inner ℂ (complexEvaluate A hA ξ f) (complexEvaluate A hA ξ g)=
      inner ℂ (ContinuousMap.toLp 2 (measure A hA ξ) ℂ f)
        (ContinuousMap.toLp 2 (measure A hA ξ) ℂ g) := by
  rw [ContinuousMap.inner_toLp]
  have hi := integral_complex A hA ξ (star f*g)
  rw [map_mul,map_star] at hi
  change (∫ x, star (f x)*g x ∂measure A hA ξ)=
    inner ℂ ξ (star (complexHom A hA f) (complexHom A hA g ξ)) at hi
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at hi
  refine hi.symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with x
  exact mul_comm _ _

 theorem complexEvaluate_norm (f : C(Space A,ℂ)) :
    ‖complexEvaluate A hA ξ f‖=‖ContinuousMap.toLp 2 (measure A hA ξ) ℂ f‖ := by
  have he := complexEvaluate_inner A hA ξ f f
  have hr : ‖complexEvaluate A hA ξ f‖^2=‖ContinuousMap.toLp 2 (measure A hA ξ) ℂ f‖^2 := by
    calc
      _ = (inner ℂ (complexEvaluate A hA ξ f) (complexEvaluate A hA ξ f)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = _ := congrArg Complex.re he
      _ = _ := inner_self_eq_norm_sq (𝕜 := ℂ) _
  nlinarith [norm_nonneg (complexEvaluate A hA ξ f),norm_nonneg (ContinuousMap.toLp 2 (measure A hA ξ) ℂ f)]

def complexRealize : Lp ℂ 2 (measure A hA ξ) →L[ℂ] H :=
  (complexEvaluate A hA ξ).extendOfNorm (ContinuousMap.toLp 2 (measure A hA ξ) ℂ).toLinearMap

 theorem complexRealize_continuous (f : C(Space A,ℂ)) :
    complexRealize A hA ξ (ContinuousMap.toLp 2 (measure A hA ξ) ℂ f)=complexHom A hA f ξ := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange ℂ (measure A hA ξ) ℂ (p := 2) (by norm_num)
  · refine ⟨1,fun g => ?_⟩
    change ‖complexEvaluate A hA ξ g‖ ≤ 1 * ‖ContinuousMap.toLp 2 (measure A hA ξ) ℂ g‖
    rw [one_mul,complexEvaluate_norm]

 theorem complexRealize_norm (f : Lp ℂ 2 (measure A hA ξ)) : ‖complexRealize A hA ξ f‖=‖f‖ := by
  have hd := ContinuousMap.toLp_denseRange ℂ (measure A hA ξ) ℂ (p := 2) (by norm_num : (2:ℝ≥0∞)≠∞)
  refine hd.induction_on (p := fun f => ‖complexRealize A hA ξ f‖=‖f‖) f
    (isClosed_eq ((complexRealize A hA ξ).continuous.norm) continuous_norm) ?_
  intro q
  rw [complexRealize_continuous]
  exact complexEvaluate_norm A hA ξ q

def complexIsometry : Lp ℂ 2 (measure A hA ξ) →ₗᵢ[ℂ] H where
  toLinearMap := (complexRealize A hA ξ).toLinearMap
  norm_map' := complexRealize_norm A hA ξ

end FreeGroupFactorMain.CyclicSpectral
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal
namespace FreeGroupFactorMain.ProbabilityTransform

section
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

 theorem continuous_cdf : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(cdf μ).rightLim_eq]
  apply le_antisymm ((cdf μ).mono.leftLim_le le_rfl)
  have h : ENNReal.ofReal (cdf μ x-leftLim (cdf μ) x)=0 := by
    rw [← (cdf μ).measure_singleton,measure_cdf,measure_singleton]
  exact sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp h)

 theorem level_greatest (r : ℝ) (hr : 0<r) (hr1 : r<1) :
    ∃ x : ℝ, cdf μ x=r ∧ ∀ y, cdf μ y≤r ↔ y≤x := by
  obtain ⟨a,ha⟩ := ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hr)).exists
  obtain ⟨b,hb⟩ := ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hr1)).exists
  have hab : a≤b := le_of_not_gt (fun h => (not_le_of_gt (ha.trans hb)) ((cdf μ).mono h.le))
  have hne : ({x:ℝ | cdf μ x=r}:Set ℝ).Nonempty := by
    obtain ⟨x,_,hxr⟩ := intermediate_value_Icc hab (continuous_cdf μ).continuousOn ⟨ha.le,hb.le⟩
    exact ⟨x,hxr⟩
  have hsub : {x:ℝ | cdf μ x=r} ⊆ Icc a b := by
    intro x hx
    constructor
    · apply le_of_not_gt
      intro h
      have hh := (cdf μ).mono h.le
      rw [hx] at hh
      exact (not_le_of_gt ha) hh
    · exact le_of_not_gt (fun h => (not_le_of_gt hb) ((cdf μ).mono h.le |>.trans_eq hx))
  have hc : IsCompact {x:ℝ | cdf μ x=r} :=
    isCompact_Icc.of_isClosed_subset (isClosed_eq (continuous_cdf μ) continuous_const) hsub
  obtain ⟨x,hx,hmax⟩ := hc.exists_isGreatest hne
  refine ⟨x,hx,fun y => ⟨fun hy => ?_,fun hy => ((cdf μ).mono hy).trans_eq hx⟩⟩
  by_contra h
  have hxy : x≤y := (lt_of_not_ge h).le
  exact h (hmax (le_antisymm hy (hx ▸ (cdf μ).mono hxy)))

 theorem measure_cdf_sublevel (r : ℝ) (hr : 0<r) (hr1 : r<1) :
    μ {x:ℝ | cdf μ x≤r}=ENNReal.ofReal r := by
  obtain ⟨x,hx,he⟩ := level_greatest μ r hr hr1
  have hs : {y:ℝ | cdf μ y≤r}=Iic x := by ext y;exact he y
  rw [hs,← ofReal_cdf,hx]

 theorem measure_cdf_zero : μ {x:ℝ | cdf μ x≤0}=0 := by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let r : ℝ := min (ε:ℝ) (1/2)
  have hr : 0<r := lt_min (by exact_mod_cast hε) (by norm_num)
  have hr1 : r<1 := (min_le_right _ _).trans_lt (by norm_num)
  rw [zero_add]
  calc
    _ ≤ μ {x:ℝ | cdf μ x≤r} := measure_mono (fun x hx => hx.trans hr.le)
    _ = ENNReal.ofReal r := measure_cdf_sublevel μ r hr hr1
    _ ≤ ENNReal.ofReal (ε:ℝ) := ENNReal.ofReal_le_ofReal (min_le_left _ _)
    _ = (ε:ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

 theorem map_cdf : Measure.map (cdf μ) μ=volume.restrict (Icc (0:ℝ) 1) := by
  apply Measure.ext_of_Iic
  intro r
  rw [Measure.map_apply (continuous_cdf μ).measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  have hs : Iic r ∩ Icc (0:ℝ) 1=Icc 0 (min r 1) := by
    ext x
    simp only [mem_inter_iff,mem_Iic,mem_Icc,le_min_iff]
    tauto
  rw [hs,Real.volume_Icc,sub_zero]
  change μ {x:ℝ | cdf μ x≤r}=ENNReal.ofReal (min r 1)
  by_cases hr : 0<r
  · by_cases hr1 : r<1
    · rw [min_eq_left hr1.le]
      exact measure_cdf_sublevel μ r hr hr1
    · have hr1' : 1≤r := le_of_not_gt hr1
      have huniv : {x:ℝ | cdf μ x≤r}=univ := by
        ext x
        simp only [mem_ofPred_eq,mem_univ,iff_true]
        exact (cdf_le_one μ x).trans hr1'
      rw [huniv,measure_univ,min_eq_right hr1',ENNReal.ofReal_one]
  · have hr' : r≤0 := le_of_not_gt hr
    have hz : μ {x:ℝ | cdf μ x≤r}=0 := by
      apply le_antisymm _ zero_le
      calc
        _ ≤ μ {x:ℝ | cdf μ x≤0} := measure_mono (fun x hx => hx.trans hr')
        _ = 0 := measure_cdf_zero μ
    rw [hz,ENNReal.ofReal_eq_zero.mpr ((min_le_left _ _).trans hr')]

end
section
open MeasureTheory ProbabilityTheory Set
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

def phase (x : ℝ) : ℂ := Complex.exp ((2*Real.pi*Complex.I)*x)

 theorem phase_continuous : Continuous phase := by
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

 theorem phase_star_mul (x : ℝ) : star (phase x)*phase x=1 := by
  change (starRingEnd ℂ) (Complex.exp ((2*Real.pi*Complex.I)*x))*Complex.exp ((2*Real.pi*Complex.I)*x)=1
  rw [← Complex.exp_conj,← Complex.exp_add]
  have he : (starRingEnd ℂ) ((2*Real.pi*Complex.I)*x)+(2*Real.pi*Complex.I)*x=0 := by
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,map_ofNat]
    ring
  rw [he,Complex.exp_zero]

 theorem phase_uniform_moment (n : ℕ) :
    ∫ x:ℝ, phase x^n ∂volume.restrict (Icc (0:ℝ) 1) = if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · simp [hn,Measure.real,Real.volume_Icc]
  · rw [ite_eq_right hn]
    have hrew (x : ℝ) : phase x^n=Complex.exp ((n:ℂ)*(2*Real.pi*Complex.I)*x) := by
      rw [phase,← Complex.exp_nat_mul]
      congr 1
      ring
    simp_rw [hrew]
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    have hc : (n:ℂ)*(2*Real.pi*Complex.I)≠0 := by
      apply mul_ne_zero (by exact_mod_cast hn)
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one,mul_one,Complex.ofReal_zero,mul_zero,Complex.exp_zero]
    have he : Complex.exp ((n:ℂ)*(2*Real.pi*Complex.I))=1 := by
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (n:ℤ)
    rw [he,sub_self,zero_div]

 theorem phase_cdf_moment (n : ℕ) :
    ∫ x:ℝ, phase (cdf μ x)^n ∂μ=if n=0 then 1 else 0 := by
  have hi := integral_map (μ := μ) (continuous_cdf μ).measurable.aemeasurable
    (phase_continuous.pow n).aestronglyMeasurable
  rw [map_cdf μ] at hi
  exact hi.symm.trans (phase_uniform_moment n)

end
section
open MeasureTheory ProbabilityTheory Set Filter
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

 theorem measure_cdf_le (r : ℝ) (hr : 0≤r) (hr1 : r≤1) :
    μ {x:ℝ | cdf μ x≤r}=ENNReal.ofReal r := by
  by_cases h0 : r=0
  · subst r
    simpa using measure_cdf_zero μ
  by_cases h1 : r=1
  · subst r
    have hs : {x:ℝ | cdf μ x≤1}=univ := by
      ext x
      simp [cdf_le_one]
    rw [hs,measure_univ,ENNReal.ofReal_one]
  exact measure_cdf_sublevel μ r (lt_of_le_of_ne hr (Ne.symm h0)) (lt_of_le_of_ne hr1 h1)

 theorem cdf_cut_ae (r : ℝ) : ∀ᵐ x ∂μ, x≤r ↔ cdf μ x≤cdf μ r := by
  have he : (Iic r : Set ℝ)=ᵐ[μ] {x:ℝ | cdf μ x≤cdf μ r} := by
    apply ae_eq_of_subset_of_measure_ge
    · exact fun x hx => (cdf μ).mono hx
    · rw [measure_cdf_le μ _ (cdf_nonneg μ r) (cdf_le_one μ r),ofReal_cdf]
    · exact measurableSet_Iic.nullMeasurableSet
    · exact measure_ne_top _ _
  filter_upwards [he] with x hx
  exact iff_of_eq hx

 theorem cdf_injective_conull :
    ∃ s : Set ℝ, μ sᶜ=0 ∧ Set.InjOn (cdf μ) s := by
  let s : Set ℝ := {x | ∀ q:ℚ, x≤(q:ℝ) ↔ cdf μ x≤cdf μ (q:ℝ)}
  refine ⟨s,?_,?_⟩
  · have he : ∀ᵐ x ∂μ, ∀ q:ℚ, x≤(q:ℝ) ↔ cdf μ x≤cdf μ (q:ℝ) :=
      ae_all_iff.mpr (fun q => cdf_cut_ae μ (q:ℝ))
    exact ae_iff.mp he
  · intro x hx y hy hxy
    apply le_antisymm
    · by_contra h
      obtain ⟨q,hyq,hqx⟩ := exists_rat_btwn (lt_of_not_ge h)
      have hyc := (hy q).mp hyq.le
      rw [← hxy] at hyc
      exact (not_le_of_gt hqx) ((hx q).mpr hyc)
    · by_contra h
      obtain ⟨q,hxq,hqy⟩ := exists_rat_btwn (lt_of_not_ge h)
      have hxc := (hx q).mp hxq.le
      rw [hxy] at hxc
      exact (not_le_of_gt hqy) ((hy q).mpr hxc)

 theorem cdf_between_ae : ∀ᵐ x ∂μ, 0<cdf μ x ∧ cdf μ x<1 := by
  have hpoint (r:ℝ) : μ {x:ℝ | cdf μ x=r}=0 := by
    change μ ((cdf μ) ⁻¹' {r})=0
    rw [← Measure.map_apply (continuous_cdf μ).measurable (measurableSet_singleton r),map_cdf,measure_singleton]
  have hz : ∀ᵐ x ∂μ, cdf μ x≠0 := by
    rw [ae_iff]
    simpa only [not_not] using hpoint 0
  have ho : ∀ᵐ x ∂μ, cdf μ x≠1 := by
    rw [ae_iff]
    simpa only [not_not] using hpoint 1
  filter_upwards [hz,ho] with x hx hy
  exact ⟨lt_of_le_of_ne (cdf_nonneg μ x) (Ne.symm hx),lt_of_le_of_ne (cdf_le_one μ x) hy⟩

 theorem phase_injectiveOn : Set.InjOn phase (Ioo (0:ℝ) 1) := by
  intro x hx y hy hxy
  obtain ⟨n,hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hxy
  have hi := congrArg Complex.im hn
  simp only [Complex.add_im,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.intCast_re,Complex.intCast_im,
    zero_mul,mul_zero,mul_one,sub_zero,add_zero,zero_add] at hi
  norm_num at hi
  have he : x=y+(n:ℝ) := by nlinarith [Real.pi_pos]
  have hl : (-1:ℝ)<(n:ℝ) := by linarith [hx.1,hy.2]
  have hu : (n:ℝ)<1 := by linarith [hx.2,hy.1]
  have hli : (-1:ℤ)<n := by exact_mod_cast hl
  have hui : n<(1:ℤ) := by exact_mod_cast hu
  have hn0 : n=0 := by omega
  simpa only [hn0,Int.cast_zero,add_zero] using he

 theorem phase_cdf_injective_conull :
    ∃ s : Set ℝ, μ sᶜ=0 ∧ Set.InjOn (fun x => phase (cdf μ x)) s := by
  obtain ⟨s,hs,hinj⟩ := cdf_injective_conull μ
  refine ⟨s ∩ {x | 0<cdf μ x ∧ cdf μ x<1},?_,?_⟩
  · have hs' : ∀ᵐ x ∂μ, x∈s := ae_iff.mpr hs
    exact ae_iff.mp (hs'.and (cdf_between_ae μ))
  · intro x hx y hy he
    exact hinj hx.1 hy.1 (phase_injectiveOn hx.2 hy.2 he)

end
section
open MeasureTheory ProbabilityTheory Set Filter Function
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

 theorem exists_measurable_phase_inverse :
    ∃ g : ℂ → ℝ, Measurable g ∧ ∀ᵐ x ∂μ, g (phase (cdf μ x))=x := by
  classical
  obtain ⟨s,hs,hinj⟩ := phase_cdf_injective_conull μ
  let t : Set ℝ := (toMeasurable μ sᶜ)ᶜ
  have ht : MeasurableSet t := (measurableSet_toMeasurable μ sᶜ).compl
  have hts : t ⊆ s := by
    intro x hx
    by_contra hn
    exact hx (subset_toMeasurable μ sᶜ hn)
  have htm : μ tᶜ=0 := by
    change μ ((toMeasurable μ sᶜ)ᶜ)ᶜ=0
    rw [compl_compl,measure_toMeasurable,hs]
  have hae : ∀ᵐ x ∂μ, x∈t := ae_iff.mpr htm
  obtain ⟨x,hx⟩ := hae.exists
  let : Nonempty t := ⟨⟨x,hx⟩⟩
  let : StandardBorelSpace t := ht.standardBorel
  let f : t → ℂ := fun y => phase (cdf μ y)
  have hf : Measurable f :=
    (phase_continuous.comp (continuous_cdf μ)).measurable.comp measurable_subtype_coe
  have hfi : Injective f := by
    intro y z he
    apply Subtype.ext
    exact hinj (hts y.property) (hts z.property) he
  let e : MeasurableEmbedding f := hf.measurableEmbedding hfi
  refine ⟨fun z => (e.invFun z:ℝ),measurable_subtype_coe.comp e.measurable_invFun,?_⟩
  filter_upwards [hae] with y hy
  exact congrArg Subtype.val (e.leftInverse_invFun (⟨y,hy⟩:t))

end
open MeasureTheory ProbabilityTheory Set Function Filter
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

def haarMeasure : Measure ℂ := μ.map (fun x => phase (cdf μ x))

 theorem haarTransform_measurable : Measurable (fun x => phase (cdf μ x)) :=
  (phase_continuous.comp (continuous_cdf μ)).measurable

 theorem haarTransform_preserving :
    MeasurePreserving (fun x => phase (cdf μ x)) μ (haarMeasure μ) :=
  ⟨haarTransform_measurable μ,rfl⟩

 theorem haarPullback_surjective : Function.Surjective
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x => phase (cdf μ x))
      (haarTransform_preserving μ) : Lp ℂ 2 (haarMeasure μ) →ₗᵢ[ℂ] Lp ℂ 2 μ) := by
  obtain ⟨g,hg,hleft⟩ := exists_measurable_phase_inverse μ
  have hpres : MeasurePreserving g (haarMeasure μ) μ := by
    refine ⟨hg,?_⟩
    change (μ.map (fun x => phase (cdf μ x))).map g=μ
    rw [Measure.map_map hg (haarTransform_measurable μ)]
    exact (Measure.map_congr hleft).trans (Measure.map_id)
  intro u
  let v := Lp.compMeasurePreserving g hpres u
  refine ⟨v,?_⟩
  apply Lp.ext
  have hv := (haarTransform_preserving μ).quasiMeasurePreserving.ae
    (Lp.coeFn_compMeasurePreserving u hpres)
  have hc := Lp.coeFn_compMeasurePreserving v (haarTransform_preserving μ)
  filter_upwards [hc,hv,hleft] with x hxc hxv hxl
  exact hxc.trans (hxv.trans (congrArg (fun y => u y) hxl))

noncomputable def haarL2Equiv : Lp ℂ 2 (haarMeasure μ) ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x => phase (cdf μ x)) (haarTransform_preserving μ))
    (haarPullback_surjective μ)

 theorem haarL2Equiv_apply (u : Lp ℂ 2 (haarMeasure μ)) :
    haarL2Equiv μ u =ᵐ[μ] fun x => u (phase (cdf μ x)) :=
  Lp.coeFn_compMeasurePreserving u (haarTransform_preserving μ)

instance haarMeasure_probability : IsProbabilityMeasure (haarMeasure μ) :=
  (Measure.isProbabilityMeasure_map_iff (haarTransform_measurable μ).aemeasurable).mpr
    inferInstance

 theorem haar_boundedContinuous_dense : DenseRange
    (fun f : BoundedContinuousFunction ℂ ℂ => haarL2Equiv μ
      (BoundedContinuousFunction.toLp 2 (haarMeasure μ) ℂ f)) := by
  exact (haarL2Equiv μ).surjective.denseRange.comp
    (BoundedContinuousFunction.toLp_denseRange ℂ (haarMeasure μ) ℂ (p := 2) (by norm_num))
    (haarL2Equiv μ).continuous

end FreeGroupFactorMain.ProbabilityTransform
namespace FreeGroupFactorMain.SpectralPullback
open MeasureTheory Function Filter
variable {X : Type u_5} {Y : Type u_6} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) {f : X → Y} (e : MeasurableEmbedding f) [Nonempty X]

theorem pullback_surjective : Function.Surjective
    (Lp.compMeasurePreservingₗᵢ ℂ f ⟨e.measurable,rfl⟩ :
      Lp ℂ 2 (μ.map f) →ₗᵢ[ℂ] Lp ℂ 2 μ) := by
  have hleft : e.invFun ∘ f=id := funext e.leftInverse_invFun
  have hpres : MeasurePreserving e.invFun (μ.map f) μ := by
    refine ⟨e.measurable_invFun,?_⟩
    rw [Measure.map_map e.measurable_invFun e.measurable,hleft,Measure.map_id]
  intro u
  let v := Lp.compMeasurePreserving e.invFun hpres u
  let hp : MeasurePreserving f μ (μ.map f) := ⟨e.measurable,rfl⟩
  refine ⟨v,?_⟩
  apply Lp.ext
  have hv := hp.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving u hpres)
  have hc := Lp.coeFn_compMeasurePreserving v hp
  filter_upwards [hc,hv] with x hxc hxv
  exact hxc.trans (hxv.trans (congrArg (fun y => u y) (e.leftInverse_invFun x)))

noncomputable def equivalence : Lp ℂ 2 (μ.map f) ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ f ⟨e.measurable,rfl⟩)
    (pullback_surjective μ e)

 theorem equivalence_apply (u : Lp ℂ 2 (μ.map f)) :
    equivalence μ e u =ᵐ[μ] fun x => u (f x) :=
  Lp.coeFn_compMeasurePreserving u ⟨e.measurable,rfl⟩
end FreeGroupFactorMain.SpectralPullback
namespace FreeGroupFactorMain.CyclicSpectral

section
open MeasureTheory ProbabilityTheory Set
variable {H : Type u_7} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def realMeasure : Measure ℝ := Measure.map (fun x : Space A => (x:ℝ)) (measure A hA ξ)

instance realMeasure_probability [IsProbabilityMeasure (measure A hA ξ)] :
    IsProbabilityMeasure (realMeasure A hA ξ) :=
  (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance

instance realMeasure_noAtoms [NullSingletonClass (measure A hA ξ)] :
    NullSingletonClass (realMeasure A hA ξ) where
  measure_singleton x := by
    rw [realMeasure,Measure.map_apply measurable_subtype_coe (measurableSet_singleton x)]
    by_cases hx : x ∈ Space A
    · have he : (fun y : Space A => (y:ℝ)) ⁻¹' {x}={⟨x,hx⟩} := by
        ext y
        simp only [mem_preimage,mem_singleton_iff,Subtype.ext_iff]
      rw [he,measure_singleton]
    · have he : (fun y : Space A => (y:ℝ)) ⁻¹' {x}=∅ := by
        ext y
        simp only [mem_preimage,mem_singleton_iff,mem_empty_iff_false,iff_false]
        intro hy
        exact hx (hy ▸ y.property)
      rw [he,measure_empty]

variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

def haarFunction : C(Space A,ℂ) :=
  ⟨fun x => ProbabilityTransform.phase (cdf (realMeasure A hA ξ) x),
    ProbabilityTransform.phase_continuous.comp
      ((ProbabilityTransform.continuous_cdf (realMeasure A hA ξ)).comp continuous_subtype_val)⟩

 theorem haarFunction_unitary : haarFunction A hA ξ ∈ unitary C(Space A,ℂ) := by
  apply Unitary.mem_iff.mpr
  constructor
  · ext x
    change star (ProbabilityTransform.phase _)*ProbabilityTransform.phase _=1
    exact ProbabilityTransform.phase_star_mul _
  · ext x
    change ProbabilityTransform.phase _*star (ProbabilityTransform.phase _)=1
    rw [mul_comm]
    exact ProbabilityTransform.phase_star_mul _

def haarUnitary : unitary (H →L[ℂ] H) :=
  ⟨complexHom A hA (haarFunction A hA ξ),Unitary.map_mem (complexHom A hA) (haarFunction_unitary A hA ξ)⟩

 theorem haarUnitary_moment (n : ℕ) :
    inner ℂ ξ (((haarUnitary A hA ξ : H →L[ℂ] H)^n) ξ)=if n=0 then 1 else 0 := by
  change inner ℂ ξ (((complexHom A hA (haarFunction A hA ξ))^n) ξ)=_
  rw [← map_pow,← integral_complex]
  change (∫ x:Space A, ProbabilityTransform.phase (cdf (realMeasure A hA ξ) x)^n ∂measure A hA ξ)=_
  have hi := integral_map (μ := measure A hA ξ) measurable_subtype_coe.aemeasurable
    (((ProbabilityTransform.phase_continuous.comp
      (ProbabilityTransform.continuous_cdf (realMeasure A hA ξ))).pow n).aestronglyMeasurable)
  exact hi.symm.trans (ProbabilityTransform.phase_cdf_moment (realMeasure A hA ξ) n)

end
section
open MeasureTheory Set Function Filter
variable {H : Type u_8} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

noncomputable def realL2Equiv : Lp ℂ 2 (realMeasure A hA ξ) ≃ₗᵢ[ℂ] Lp ℂ 2 (measure A hA ξ) := by
  let : Nonempty (Space A) := nonempty_of_isProbabilityMeasure (measure A hA ξ)
  exact SpectralPullback.equivalence (measure A hA ξ)
    (MeasurableEmbedding.subtype_coe (spectrum.isClosed A).measurableSet)

omit [NullSingletonClass (measure A hA ξ)] in
 theorem realL2Equiv_apply (u : Lp ℂ 2 (realMeasure A hA ξ)) :
    realL2Equiv A hA ξ u =ᵐ[measure A hA ξ] fun x => u (x:ℝ) := by
  exact Lp.coeFn_compMeasurePreserving u ⟨measurable_subtype_coe,rfl⟩

noncomputable def haarSpectralTransfer :
    Lp ℂ 2 (ProbabilityTransform.haarMeasure (realMeasure A hA ξ)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (measure A hA ξ) :=
  (ProbabilityTransform.haarL2Equiv (realMeasure A hA ξ)).trans (realL2Equiv A hA ξ)

 theorem haarSpectralTransfer_continuous (q : BoundedContinuousFunction ℂ ℂ) :
    haarSpectralTransfer A hA ξ
        (BoundedContinuousFunction.toLp 2 (ProbabilityTransform.haarMeasure (realMeasure A hA ξ)) ℂ q)
      = ContinuousMap.toLp 2 (measure A hA ξ) ℂ (q.toContinuousMap.comp (haarFunction A hA ξ)) := by
  let μ := realMeasure A hA ξ
  let u := BoundedContinuousFunction.toLp 2 (ProbabilityTransform.haarMeasure μ) ℂ q
  let hp : MeasurePreserving (fun x : Space A => (x:ℝ)) (measure A hA ξ) μ :=
    ⟨measurable_subtype_coe,rfl⟩
  have h1 := realL2Equiv_apply A hA ξ (ProbabilityTransform.haarL2Equiv μ u)
  have h2 := hp.quasiMeasurePreserving.ae (ProbabilityTransform.haarL2Equiv_apply μ u)
  have h3 := hp.quasiMeasurePreserving.ae
    ((ProbabilityTransform.haarTransform_preserving μ).quasiMeasurePreserving.ae
      (BoundedContinuousFunction.coeFn_toLp 2 (ProbabilityTransform.haarMeasure μ) ℂ q))
  have h4 := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (measure A hA ξ) (q.toContinuousMap.comp (haarFunction A hA ξ))
  apply Lp.ext
  filter_upwards [h1,h2,h3,h4] with x hx1 hx2 hx3 hx4
  exact hx1.trans (hx2.trans (hx3.trans hx4.symm))

 theorem haar_spectral_functions_dense : DenseRange
    (fun q : BoundedContinuousFunction ℂ ℂ => ContinuousMap.toLp 2 (measure A hA ξ) ℂ
      (q.toContinuousMap.comp (haarFunction A hA ξ))) := by
  have hd := (haarSpectralTransfer A hA ξ).surjective.denseRange.comp
    (BoundedContinuousFunction.toLp_denseRange ℂ
      (ProbabilityTransform.haarMeasure (realMeasure A hA ξ)) ℂ (p := 2) (by norm_num))
    (haarSpectralTransfer A hA ξ).continuous
  convert hd using 1
  funext q
  exact (haarSpectralTransfer_continuous A hA ξ q).symm

end
section
open MeasureTheory Set Function Filter
variable {H : Type u_9} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

 theorem haar_cyclic_contains_continuous (f : C(Space A,ℂ)) :
    complexHom A hA f ξ ∈ closure (Set.range (fun q : BoundedContinuousFunction ℂ ℂ =>
      complexHom A hA (q.toContinuousMap.comp (haarFunction A hA ξ)) ξ)) := by
  let s := closure (Set.range (fun q : BoundedContinuousFunction ℂ ℂ =>
    complexHom A hA (q.toContinuousMap.comp (haarFunction A hA ξ)) ξ))
  have hd := haar_spectral_functions_dense A hA ξ
  have hall : ∀ v : Lp ℂ 2 (measure A hA ξ), complexRealize A hA ξ v ∈ s := by
    intro v
    refine hd.induction_on (p := fun v => complexRealize A hA ξ v ∈ s) v
      (isClosed_closure.preimage (complexRealize A hA ξ).continuous) ?_
    intro q
    rw [complexRealize_continuous]
    exact subset_closure (Set.mem_range_self q)
  simpa only [complexRealize_continuous] using hall (ContinuousMap.toLp 2 (measure A hA ξ) ℂ f)

 theorem haar_cyclic_contains_operator :
    A ξ ∈ closure (Set.range (fun q : BoundedContinuousFunction ℂ ℂ =>
      complexHom A hA (q.toContinuousMap.comp (haarFunction A hA ξ)) ξ)) := by
  have h := haar_cyclic_contains_continuous A hA ξ
    (complexLift A ((ContinuousMap.id ℝ).restrict (spectrum ℝ A)))
  rwa [complexHom_real,cfcHom_id] at h

end
section
variable {H : Type u_10} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)

 theorem complexHom_continuous : Continuous (complexHom A hA) := by
  exact AddMonoidHomClass.continuous_of_bound (complexHom A hA) 1
    (by simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le (complexHom A hA))

 theorem complexHom_composition (f : C(Space A,ℂ)) (q : C(ℂ,ℂ)) :
    complexHom A hA (q.comp f)=cfc q (complexHom A hA f) := by
  have he : cfc q f=q.comp f := by
    ext x
    have hh := (ContinuousMap.evalStarAlgHom ℂ ℂ x).map_cfc q f
      q.continuous.continuousOn (continuous_eval_const x)
    change cfc q f x=cfc q (f x) at hh
    rw [hh]
    exact cfc_algebraMap (A := ℂ) (f x) q
  rw [← he]
  exact (complexHom A hA).map_cfc q f q.continuous.continuousOn (complexHom_continuous A hA)

 theorem complexHom_composition_mem (f : C(Space A,ℂ)) (q : C(ℂ,ℂ))
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
    (hf : complexHom A hA f ∈ S) : complexHom A hA (q.comp f) ∈ S := by
  rw [complexHom_composition]
  apply StarSubalgebra.topologicalClosure_minimal (t := S) (by simpa) hS
    (cfc_mem_elemental _ _)

end
section
open MeasureTheory Set Function Filter

def scalarClip (R : ℝ) (z : ℂ) : ℂ := (max (-R) (min R z.re) : ℝ)
 theorem continuous_scalarClip (R : ℝ) : Continuous (scalarClip R) := by
  unfold scalarClip
  fun_prop
 theorem norm_scalarClip (R : ℝ) (hR : 0 ≤ R) (z : ℂ) : ‖scalarClip R z‖ ≤ R := by
  simp only [scalarClip,Complex.norm_real,Real.norm_eq_abs,abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
 theorem scalarClip_error (R x : ℝ) (hx : |x| ≤ R) (z : ℂ) :
    ‖scalarClip R z-(x:ℂ)‖ ≤ ‖z-(x:ℂ)‖ := by
  have hx' := abs_le.mp hx
  have he : |max (-R) (min R z.re)-x| ≤ |z.re-x| := by
    by_cases hz : z.re ≤ R
    · rw [min_eq_right hz]
      by_cases hl : -R ≤ z.re
      · rw [max_eq_right hl]
      · rw [max_eq_left (le_of_not_ge hl),abs_of_nonpos (by linarith)]
        exact (by linarith [neg_le_abs (z.re-x)])
    · rw [min_eq_left (le_of_not_ge hz),max_eq_right (by linarith),abs_of_nonneg (by linarith)]
      exact (by linarith [le_abs_self (z.re-x)])
  calc
    _ = |max (-R) (min R z.re)-x| := by
      rw [scalarClip,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ |z.re-x| := he
    _ ≤ _ := by simpa using Complex.abs_re_le_norm (z-(x:ℂ))

variable {H : Type u_11} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def clipFunction (q : C(ℂ,ℂ)) : C(ℂ,ℂ) := ⟨scalarClip ‖A‖ ∘ q,(continuous_scalarClip ‖A‖).comp q.continuous⟩

 theorem clipFunction_norm (q : C(ℂ,ℂ)) (f : C(Space A,ℂ)) :
    ‖complexHom A hA ((clipFunction A q).comp f)‖ ≤ ‖A‖ := by
  apply (NonUnitalStarAlgHom.norm_apply_le _ _).trans
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  exact norm_scalarClip ‖A‖ (norm_nonneg _) _
end
open MeasureTheory Set Function Filter
variable {H : Type u_12} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

def coordinate : C(Space A,ℂ) := complexLift A ((ContinuousMap.id ℝ).restrict (spectrum ℝ A))
omit [Nontrivial H] in
 theorem complexHom_coordinate : complexHom A hA (coordinate A)=A := by
  rw [coordinate,complexHom_real,cfcHom_id]

omit [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)] in
 theorem clip_vector_error (q : C(ℂ,ℂ)) (f : C(Space A,ℂ)) :
    ‖complexHom A hA ((clipFunction A q).comp f) ξ-A ξ‖ ≤
      ‖complexHom A hA (q.comp f) ξ-A ξ‖ := by
  have hc : A ξ=complexHom A hA (coordinate A) ξ :=
    congrArg (fun T : H →L[ℂ] H => T ξ) (complexHom_coordinate A hA).symm
  rw [hc]
  have heval (g : C(Space A,ℂ)) : complexEvaluate A hA ξ (g-coordinate A)=
      complexHom A hA g ξ-complexHom A hA (coordinate A) ξ := by
    simp [complexEvaluate]
  rw [← heval,← heval]
  rw [complexEvaluate_norm,complexEvaluate_norm]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (measure A hA ξ)
      (((clipFunction A q).comp f)-coordinate A),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (measure A hA ξ) (q.comp f-coordinate A)] with x h1 h2
  rw [h1,h2]
  apply scalarClip_error
  change |(x:ℝ)| ≤ ‖A‖
  simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem x.property

 theorem bounded_haar_approx (ε : ℝ) (hε : 0 < ε) :
    ∃ T : H →L[ℂ] H,
      T ∈ StarAlgebra.elemental ℂ (haarUnitary A hA ξ : H →L[ℂ] H) ∧
      ‖T‖ ≤ ‖A‖ ∧ ‖T ξ-A ξ‖ < ε := by
  obtain ⟨v,⟨q,rfl⟩,hq⟩ := Metric.mem_closure_iff.mp
    (haar_cyclic_contains_operator A hA ξ) ε hε
  refine ⟨complexHom A hA ((clipFunction A q.toContinuousMap).comp (haarFunction A hA ξ)),?_,
    clipFunction_norm A hA _ _,?_⟩
  · apply complexHom_composition_mem
    · exact StarAlgebra.elemental.isClosed _ _
    · exact StarAlgebra.elemental.self_mem _ _
  · exact (clip_vector_error A hA ξ _ _).trans_lt (by simpa only [dist_eq_norm,norm_sub_rev] using hq)
end FreeGroupFactorMain.CyclicSpectral
namespace FreeGroupFactorMain
open Filter Topology
variable {E : Type u_13} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem strong_limit_of_bounded_total {ι : Type u_14}
    (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E) (C : ℝ) (hbound : ∀ n, ‖T n‖ ≤ C)
    (v : ι → E) (htotal : (Submodule.span ℂ (Set.range v)).topologicalClosure=⊤)
    (hv : ∀ i, Tendsto (fun n => T n (v i)) atTop (𝓝 (A (v i))))
    (ξ : E) : Tendsto (fun n => T n ξ) atTop (𝓝 (A ξ)) := by
  have heq : Equicontinuous (fun n => (T n : E → E)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => C*r)
      (by simpa using (tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))))
    intro x y n
    rw [dist_eq_norm,← map_sub]
    exact (T n).le_opNorm (x-y) |>.trans
      (by simpa only [dist_eq_norm] using mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg (x-y)))
  let L : Submodule ℂ E := {
    carrier := {ξ | Tendsto (fun n => T n ξ) atTop (𝓝 (A ξ))}
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy
      simpa only [Set.mem_ofPred_eq,map_add] using hx.add hy
    smul_mem' := by
      intro c x hx
      simpa only [Set.mem_ofPred_eq,map_smul] using hx.const_smul c }
  have hclosed : IsClosed (L : Set E) := heq.isClosed_setOfPred_tendsto A.continuous
  have hle : Submodule.span ℂ (Set.range v) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hv i)
  have hh := Submodule.topologicalClosure_minimal _ hle hclosed
  rw [htotal] at hh
  exact hh (Submodule.mem_top)
end FreeGroupFactorMain

namespace FreeGroupFactorMain.CyclicSpectral
open Filter Topology Set MeasureTheory
variable {E : Type u_15} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
variable (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (ξ : E)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

theorem operator_mem_haar_bicommutant (M : StarSubalgebra ℂ (E →L[ℂ] E))
    (hM : IsClosed (M : Set (E →L[ℂ] E))) (hAM : A∈M)
    (htotal : (Submodule.span ℂ (Set.range (fun B : StarSubalgebra.centralizer ℂ (M : Set (E →L[ℂ] E)) =>
      (B : E →L[ℂ] E) ξ))).topologicalClosure=⊤) :
    A ∈ StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
      ({(haarUnitary A hA ξ : E →L[ℂ] E)} : Set (E →L[ℂ] E)) : Set (E →L[ℂ] E)) := by
  have hU : (haarUnitary A hA ξ : E →L[ℂ] E)∈M := by
    exact complexHom_mem A hA M hM hAM _
  have hb (n : ℕ) := bounded_haar_approx A hA ξ (1/((n:ℝ)+1)) (by positivity)
  choose T hmem hnorm herr using hb
  have hT (n : ℕ) : T n∈M := StarAlgebra.elemental.le_of_mem hM hU (hmem n)
  have hv : Tendsto (fun n => T n ξ) atTop (𝓝 (A ξ)) := by
    have h := squeeze_zero_norm (fun n => (herr n).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [sub_add_cancel,zero_add] using h.add_const (A ξ)
  have hstrong : ∀ ζ, Tendsto (fun n => T n ζ) atTop (𝓝 (A ζ)) := by
    apply strong_limit_of_bounded_total T A ‖A‖ hnorm _ htotal
    intro B
    have hB (D : E →L[ℂ] E) (hD : D∈M) : D ((B : E →L[ℂ] E) ξ)=(B : E →L[ℂ] E) (D ξ) :=
      DFunLike.congr_fun (((StarSubalgebra.mem_centralizer_iff ℂ).mp B.property D hD).1) ξ
    simpa only [hB _ (hT _),hB _ hAM,Function.comp_def] using
      (B : E →L[ℂ] E).continuous.continuousAt.tendsto.comp hv
  let N := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
      ({(haarUnitary A hA ξ : E →L[ℂ] E)} : Set (E →L[ℂ] E)) : Set (E →L[ℂ] E))
  have hN : IsClosed (N : Set (E →L[ℂ] E)) := Set.isClosed_centralizer _
  have hUN : (haarUnitary A hA ξ : E →L[ℂ] E)∈N :=
    StarAlgebra.adjoin_le_centralizer_centralizer ℂ _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_singleton _))
  have hTN (n : ℕ) : T n∈N := StarAlgebra.elemental.le_of_mem hN hUN (hmem n)
  rw [StarSubalgebra.mem_centralizer_iff]
  intro B hB
  have hb' (D : E →L[ℂ] E) (hD : D∈StarSubalgebra.centralizer ℂ
      ({(haarUnitary A hA ξ : E →L[ℂ] E)} : Set (E →L[ℂ] E))) : D*A=A*D := by
    ext ζ
    have he n := congrArg (fun Q : E →L[ℂ] E => Q ζ)
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hTN n) D hD).1
    exact tendsto_nhds_unique ((D.continuous.continuousAt.tendsto.comp (hstrong ζ)).congr
      (fun n => he n)) (hstrong (D ζ))
  exact ⟨hb' B hB,hb' (star B) (star_mem hB)⟩
end FreeGroupFactorMain.CyclicSpectral

end

end OAI
