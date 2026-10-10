import OAI.Probability.GaussianReplacement.Mixture

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def cauchyObservation {d : ℕ} {C : Type*} (z : (C×Sphere d)×(Vector d×Vector d)) :
    ((C×(Vector d×Vector d))×ℝ)×ℝ :=
  (((z.1.1,z.2),⟪(z.1.2:Vector d),z.2.1⟫),⟪(z.1.2:Vector d),z.2.2⟫)

lemma measurable_cauchyObservation {d : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (cauchyObservation (d:=d) (C:=C)) := by
  unfold cauchyObservation
  fun_prop

def cauchyObservationLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) : Measure (((C×(Vector d×Vector d))×ℝ)×ℝ) :=
  (Γ.prod (gaussianVectorPair d)).map cauchyObservation

instance cauchyObservationLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] : IsProbabilityMeasure (cauchyObservationLaw Γ) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_cauchyObservation.aemeasurable).mpr inferInstance

lemma gaussian_inner_map_sphere {d : ℕ} (s : Sphere d) :
    (stdGaussian (Vector d)).map (fun x => ⟪(s:Vector d),x⟫) = gaussianReal 0 1 := by
  rw [gaussian_inner_map_scaled,show ‖(s:Vector d)‖ = 1 from mem_sphere_zero_iff_norm.mp s.property]
  simp only [one_mul,Measure.map_id']

lemma cauchyObservationLaw_snd {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    (cauchyObservationLaw Γ).snd = gaussianReal 0 1 := by
  rw [Measure.snd,cauchyObservationLaw,Measure.map_map measurable_snd measurable_cauchyObservation]
  ext t ht
  rw [Measure.map_apply (by unfold cauchyObservation; fun_prop) ht,
    Measure.prod_apply (ht.preimage (by unfold cauchyObservation; fun_prop))]
  have ho (z : C×Sphere d) : gaussianVectorPair d {x | ⟪(z.2:Vector d),x.2⟫ ∈ t} = gaussianReal 0 1 t := by
    have hm : Measurable (fun x : Vector d => ⟪(z.2:Vector d),x⟫) := by fun_prop
    have he := congrArg (fun μ : Measure ℝ => μ t) (gaussian_inner_map_sphere z.2)
    rw [Measure.map_apply hm ht] at he
    change gaussianVectorPair d (Prod.snd ⁻¹' ((fun x : Vector d => ⟪(z.2:Vector d),x⟫) ⁻¹' t)) = _
    rw [←Measure.snd_apply (ht.preimage hm),Measure.snd_prod]
    exact he
  change (∫⁻ z : C×Sphere d, gaussianVectorPair d {x | ⟪(z.2:Vector d),x.2⟫ ∈ t} ∂Γ) = _
  simp_rw [ho]
  simp

lemma log_standardGaussianPDF (x : ℝ) :
    Real.log (gaussianPDFReal 0 1 x) = -Real.log (Real.sqrt (2*Real.pi))-x^2/2 := by
  change Real.log ((Real.sqrt (2*Real.pi*1))⁻¹ * Real.exp (-(x-0)^2/(2*1))) = _
  simp only [mul_one,sub_zero]
  rw [Real.log_mul (inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne') (Real.exp_pos _).ne',
    Real.log_inv,Real.log_exp]
  ring

def standardGaussianEntropy : ℝ := Real.log (Real.sqrt (2*Real.pi))+1/2

lemma standardGaussian_cross_entropy {T : Type*} [MeasurableSpace T]
    (P : Measure (T×ℝ)) [IsProbabilityMeasure P] (hm : P.snd = gaussianReal 0 1) :
    Integrable (fun z : T×ℝ => Real.log (gaussianPDFReal 0 1 z.2)) P ∧
      (∫ z : T×ℝ, -Real.log (gaussianPDFReal 0 1 z.2) ∂P) = standardGaussianEntropy := by
  have hf : Measurable (fun x : ℝ => Real.log (gaussianPDFReal 0 1 x)) := by fun_prop
  have hsq := integrable_standardNormal_square
  have hi : Integrable (fun x : ℝ => Real.log (gaussianPDFReal 0 1 x)) (gaussianReal 0 1) := by
    simp_rw [log_standardGaussianPDF]
    exact (integrable_const _).sub (hsq.div_const 2)
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).mp (by change Integrable _ P.snd; rw [hm]; exact hi),?_⟩
  have he := integral_map (μ:=P) (φ:=Prod.snd) measurable_snd.aemeasurable hf.neg.aestronglyMeasurable
  change (∫ z, (-fun x => Real.log (gaussianPDFReal 0 1 x)) z.2 ∂P) = _
  rw [←he]
  change (∫ x, -Real.log (gaussianPDFReal 0 1 x) ∂P.snd) = _
  rw [hm]
  simp_rw [log_standardGaussianPDF,neg_sub]
  rw [integral_sub (hsq.div_const 2) (integrable_const _),integral_div,integral_standardNormal_square]
  simp [standardGaussianEntropy,add_comm]

lemma cauchyMixture_experiment_bound {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ]
    (hfin : conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1) ≠ ∞)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    standardGaussianEntropy - (conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1)).toReal ≤
      cauchyTiltConstant - ∫ z : C×Sphere d, Real.log (regularizedScale (κ z.1) e z.2) ∂Γ := by
  let P := cauchyObservationLaw Γ
  let Λ := P.fst.prod (volume : Measure ℝ)
  let r : (((C×(Vector d×Vector d))×ℝ)×ℝ) → ℝ := fun z => gaussianPDFReal 0 1 z.2
  let q : (((C×(Vector d×Vector d))×ℝ)×ℝ) → ℝ :=
    fun z => cauchyMixture (κ z.1.1.1) e z.1.1.2 (z.1.2,z.2)
  have hr : Measurable r := by dsimp [r]; fun_prop
  have hq : Measurable q := (cauchyMixture_kernel_measurable κ e).comp (show Measurable (fun z : (((C×(Vector d×Vector d))×ℝ)×ℝ) => ((z.1.1.1,z.1.1.2),(z.1.2,z.2))) by fun_prop)
  have hrpos : ∀ z, 0 < r z := fun z => gaussianPDFReal_pos _ _ _ (by norm_num)
  have hqpos : ∀ z, 0 < q z := fun z => cauchyMixture_pos _ he _ _
  have hR : Λ.withDensity (fun z => ENNReal.ofReal (r z)) = P.fst.prod (gaussianReal 0 1) := by
    rw [show (fun z => ENNReal.ofReal (r z)) = (fun z => gaussianPDF 0 1 z.2) from rfl,
      ←prod_withDensity_right (measurable_gaussianPDF 0 1),gaussianReal_of_var_ne_zero 0 (by norm_num)]
  have hnorm : (∫⁻ z, ENNReal.ofReal (q z) ∂Λ) = 1 := by
    rw [lintegral_prod _ hq.ennreal_ofReal.aemeasurable]
    simp_rw [show ∀ z : (C×(Vector d×Vector d))×ℝ,
      (∫⁻ y, ENNReal.ofReal (q (z,y))) = 1 from fun z => cauchyMixture_normalization (κ z.1.1) he z.1.2 z.2]
    simp
  have hc := standardGaussian_cross_entropy P (cauchyObservationLaw_snd Γ)
  have hqi : Integrable (fun z => Real.log (q z)) P := by
    apply (integrable_map_measure hq.log.aestronglyMeasurable measurable_cauchyObservation.aemeasurable).mpr
    have hi := (ownCauchyMixture_context_integrable Γ κ he he1).neg
    convert hi using 1
    ext z
    simp [q,cauchyObservation,cauchyMixture_at_own]
  have hg := reference_gibbs P (P.fst.prod (gaussianReal 0 1)) Λ r q hr hq hrpos hqpos hR hnorm hfin hc.1 hqi
  rw [hc.2] at hg
  have heq : (∫ z, -Real.log (q z) ∂P) = ∫ z, -Real.log (ownCauchyMixture (κ z.1.1) e z.1.2 z.2)
      ∂Γ.prod (gaussianVectorPair d) := by
    rw [show P = (Γ.prod (gaussianVectorPair d)).map cauchyObservation from rfl,
      integral_map (f:=fun z => -Real.log (q z)) measurable_cauchyObservation.aemeasurable hq.log.neg.aestronglyMeasurable]
    simp only [q,cauchyObservation,cauchyMixture_at_own]
  rw [heq] at hg
  exact hg.trans (ownCauchyMixture_context_bound Γ κ he he1)



def reciprocalScale {d : ℕ} (μ : Measure (Sphere d)) (s : Sphere d) : ℝ≥0∞ :=
  ∫⁻ t, (ENNReal.ofReal (dist s t))⁻¹ ∂μ

def reciprocalCutoff (n : ℕ) : ℝ := 1/((n:ℝ)+1)

lemma reciprocalCutoff_pos (n : ℕ) : 0 < reciprocalCutoff n := by unfold reciprocalCutoff; positivity
lemma reciprocalCutoff_le_one (n : ℕ) : reciprocalCutoff n ≤ 1 := by
  unfold reciprocalCutoff
  apply (div_le_iff₀ (by positivity)).mpr
  simp
lemma reciprocalCutoff_antitone : Antitone reciprocalCutoff := by
  intro n m h
  unfold reciprocalCutoff
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right h 1
lemma reciprocalCutoff_limit : Tendsto reciprocalCutoff atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma regularizedReciprocal_monotone {d : ℕ} (s t : Sphere d) :
    Monotone (fun n => regularizedReciprocal (reciprocalCutoff n) s t) := by
  intro n m h
  unfold regularizedReciprocal
  apply inv_anti₀ (lt_of_lt_of_le (reciprocalCutoff_pos m) (le_max_right _ _))
  exact max_le_max_left _ (reciprocalCutoff_antitone h)

lemma regularizedReciprocal_limit {d : ℕ} (s t : Sphere d) :
    Tendsto (fun n => ENNReal.ofReal (regularizedReciprocal (reciprocalCutoff n) s t)) atTop
      (𝓝 (ENNReal.ofReal (dist s t))⁻¹) := by
  have hm : Tendsto (fun n => ENNReal.ofReal (max (dist s t) (reciprocalCutoff n))) atTop
      (𝓝 (ENNReal.ofReal (dist s t))) := by
    simpa only [Function.comp_def,max_eq_left dist_nonneg] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=dist s t)).max reciprocalCutoff_limit)
  have he : (fun n => ENNReal.ofReal (regularizedReciprocal (reciprocalCutoff n) s t)) =
      fun n => (ENNReal.ofReal (max (dist s t) (reciprocalCutoff n)))⁻¹ := by
    funext n
    exact ENNReal.ofReal_inv_of_pos (lt_of_lt_of_le (reciprocalCutoff_pos n) (le_max_right _ _))
  rw [he]
  exact tendsto_inv_iff.mpr hm

lemma regularizedScale_ofReal {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) :
    ENNReal.ofReal (regularizedScale μ e s) = ∫⁻ t, ENNReal.ofReal (regularizedReciprocal e s t) ∂μ :=
  ofReal_integral_eq_lintegral_ofReal (integrable_regularizedReciprocal μ he s)
    (ae_of_all _ (fun t => (regularizedReciprocal_pos he s t).le))

lemma regularizedScale_limit {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ] (s : Sphere d) :
    Tendsto (fun n => ENNReal.ofReal (regularizedScale μ (reciprocalCutoff n) s)) atTop
      (𝓝 (reciprocalScale μ s)) := by
  simp_rw [regularizedScale_ofReal μ (reciprocalCutoff_pos _)]
  exact lintegral_tendsto_of_tendsto_of_monotone
    (fun _ => (by unfold regularizedReciprocal; fun_prop))
    (ae_of_all _ (fun t => fun n m h => ENNReal.ofReal_le_ofReal (regularizedReciprocal_monotone s t h)))
    (ae_of_all _ (fun t => regularizedReciprocal_limit s t))

lemma regularizedScale_monotone {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ] (s : Sphere d) :
    Monotone (fun n => regularizedScale μ (reciprocalCutoff n) s) := by
  intro n m h
  exact integral_mono (integrable_regularizedReciprocal μ (reciprocalCutoff_pos n) s)
    (integrable_regularizedReciprocal μ (reciprocalCutoff_pos m) s)
    (fun t => regularizedReciprocal_monotone s t h)

lemma reciprocalScale_kernel_measurable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] :
    Measurable (fun z : C×Sphere d => reciprocalScale (κ z.1) z.2) := by
  exact (show Measurable (fun z : (C×Sphere d)×Sphere d => (ENNReal.ofReal (dist z.1.2 z.2))⁻¹) by
    fun_prop).lintegral_kernel_prod_right (κ:=κ.comap Prod.fst measurable_fst)

lemma regularizedScale_le_reciprocalScale {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    (s : Sphere d) (n : ℕ) :
    ENNReal.ofReal (regularizedScale μ (reciprocalCutoff n) s) ≤ reciprocalScale μ s := by
  exact ge_of_tendsto (regularizedScale_limit μ s) (eventually_atTop.mpr ⟨n,fun m hm =>
    ENNReal.ofReal_le_ofReal (regularizedScale_monotone μ s hm)⟩)

lemma reciprocalScale_lower {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ] (s : Sphere d) :
    ENNReal.ofReal (1/2:ℝ) ≤ reciprocalScale μ s :=
  (ENNReal.ofReal_le_ofReal (regularizedScale_bounds μ (reciprocalCutoff_pos 0)
    (reciprocalCutoff_le_one 0) s).1).trans (regularizedScale_le_reciprocalScale μ s 0)

def logScaleExtended (a : ℝ≥0∞) : ℝ≥0∞ := (ENNReal.log (2*a)).toENNReal

lemma continuous_logScaleExtended : Continuous logScaleExtended :=
  EReal.continuous_toENNReal.comp (ENNReal.continuous_log.comp (ENNReal.continuous_const_mul (a:=2) (by norm_num)))

lemma logScaleExtended_monotone : Monotone logScaleExtended := by
  intro a b h
  apply EReal.toENNReal_le_toENNReal
  exact ENNReal.log_le_log (mul_le_mul_right h 2)

lemma logScaleExtended_ofReal {a : ℝ} (ha : 0 < a) :
    logScaleExtended (ENNReal.ofReal a) = ENNReal.ofReal (Real.log a+Real.log 2) := by
  unfold logScaleExtended
  rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num]
  rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.log_ofReal_of_pos (by positivity),
    EReal.real_coe_toENNReal,Real.log_mul (by norm_num) ha.ne']
  congr 1
  ring

lemma logScaleExtended_top_iff (a : ℝ≥0∞) : logScaleExtended a = ∞ ↔ a = ∞ := by
  simp [logScaleExtended,ENNReal.mul_eq_top]

lemma log_add_log_two_nonneg {a : ℝ} (ha : 1/2 ≤ a) : 0 ≤ Real.log a+Real.log 2 := by
  have hp : 0 < a := lt_of_lt_of_le (by norm_num) ha
  rw [←Real.log_mul hp.ne' (by norm_num)]
  apply Real.log_nonneg
  linarith

lemma reciprocalScale_log_bound {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] {M : ℝ}
    (hb : ∀ n, (∫ z : C×Sphere d, Real.log (regularizedScale (κ z.1) (reciprocalCutoff n) z.2) ∂Γ) ≤ M) :
    (∀ᵐ z : C×Sphere d ∂Γ, reciprocalScale (κ z.1) z.2 ≠ ∞) ∧
    Integrable (fun z : C×Sphere d => Real.log (reciprocalScale (κ z.1) z.2).toReal) Γ ∧
    (∫ z : C×Sphere d, Real.log (reciprocalScale (κ z.1) z.2).toReal ∂Γ) ≤ M := by
  let f (n : ℕ) (z : C×Sphere d) := logScaleExtended (ENNReal.ofReal
    (regularizedScale (κ z.1) (reciprocalCutoff n) z.2))
  let F (z : C×Sphere d) := logScaleExtended (reciprocalScale (κ z.1) z.2)
  have hm n : Measurable (f n) := continuous_logScaleExtended.measurable.comp
    (regularizedScale_kernel_measurable κ _).ennreal_ofReal
  have hM : Measurable F := continuous_logScaleExtended.measurable.comp (reciprocalScale_kernel_measurable κ)
  have hl (n : ℕ) (z : C×Sphere d) : 1/2 ≤ regularizedScale (κ z.1) (reciprocalCutoff n) z.2 :=
    (regularizedScale_bounds _ (reciprocalCutoff_pos n) (reciprocalCutoff_le_one n) _).1
  have he n : (∫⁻ z, f n z ∂Γ) = ENNReal.ofReal ((∫ z : C×Sphere d,
      Real.log (regularizedScale (κ z.1) (reciprocalCutoff n) z.2) ∂Γ)+Real.log 2) := by
    simp_rw [f,logScaleExtended_ofReal (lt_of_lt_of_le (by norm_num) (hl n _))]
    rw [←ofReal_integral_eq_lintegral_ofReal (f:=fun z : C×Sphere d => Real.log (regularizedScale (κ z.1) (reciprocalCutoff n) z.2)+Real.log 2)
      ((regularizedScale_context_log_integrable Γ κ (reciprocalCutoff_pos n) (reciprocalCutoff_le_one n)).add (integrable_const _))
      (ae_of_all _ (fun z => log_add_log_two_nonneg (hl n z))),
      integral_add (regularizedScale_context_log_integrable Γ κ (reciprocalCutoff_pos n)
        (reciprocalCutoff_le_one n)) (integrable_const _)]
    simp
  have hn : 0 ≤ M+Real.log 2 := by
    have h := integral_nonneg (μ:=Γ) (f:=fun z : C×Sphere d => Real.log (regularizedScale (κ z.1) (reciprocalCutoff 0) z.2)+Real.log 2) (fun z => log_add_log_two_nonneg (hl 0 z))
    rw [integral_add (regularizedScale_context_log_integrable Γ κ (reciprocalCutoff_pos 0)
      (reciprocalCutoff_le_one 0)) (integrable_const _)] at h
    simp only [integral_const,probReal_univ,one_smul] at h
    linarith [hb 0]
  have ht : Tendsto (fun n => ∫⁻ z, f n z ∂Γ) atTop (𝓝 (∫⁻ z, F z ∂Γ)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone (fun n => (hm n).aemeasurable)
    · exact ae_of_all _ (fun z n m h => logScaleExtended_monotone
        (ENNReal.ofReal_le_ofReal (regularizedScale_monotone (κ z.1) z.2 h)))
    · exact ae_of_all _ (fun z => continuous_logScaleExtended.continuousAt.tendsto.comp
        (regularizedScale_limit (κ z.1) z.2))
  have hbF : (∫⁻ z, F z ∂Γ) ≤ ENNReal.ofReal (M+Real.log 2) := by
    apply le_of_tendsto' ht
    intro n
    rw [he]
    exact ENNReal.ofReal_le_ofReal (by linarith [hb n])
  have hfin : (∫⁻ z, F z ∂Γ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbF
  have haeF : ∀ᵐ z ∂Γ, F z ≠ ∞ := (ae_lt_top hM hfin).mono (fun _ h => h.ne)
  have hae : ∀ᵐ z : C×Sphere d ∂Γ, reciprocalScale (κ z.1) z.2 ≠ ∞ := by
    filter_upwards [haeF] with z hz
    exact mt (logScaleExtended_top_iff _).mpr hz
  have heF : (fun z => (F z).toReal) =ᵐ[Γ]
      fun z : C×Sphere d => Real.log (reciprocalScale (κ z.1) z.2).toReal+Real.log 2 := by
    filter_upwards [hae] with z hz
    have hlz : 1/2 ≤ (reciprocalScale (κ z.1) z.2).toReal := by
      exact (ENNReal.ofReal_le_iff_le_toReal hz).mp (reciprocalScale_lower _ _)
    have hez := logScaleExtended_ofReal (lt_of_lt_of_le (by norm_num) hlz)
    rw [ENNReal.ofReal_toReal hz] at hez
    change (logScaleExtended _).toReal = _
    rw [hez,ENNReal.toReal_ofReal (log_add_log_two_nonneg hlz)]
  have hi := integrable_toReal_of_lintegral_ne_top hM.aemeasurable hfin
  have hi' : Integrable (fun z : C×Sphere d => Real.log (reciprocalScale (κ z.1) z.2).toReal) Γ := by
    have := (hi.congr heF).sub (integrable_const (Real.log 2))
    convert this using 1
    ext z
    simp
  refine ⟨hae,hi',?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbF
  rw [ENNReal.toReal_ofReal hn,←integral_toReal hM.aemeasurable (haeF.mono (fun _ h => h.lt_top)),
    integral_congr_ae heF,integral_add hi' (integrable_const _)] at hreal
  simp only [integral_const,probReal_univ,one_smul] at hreal
  linarith

lemma reciprocalScale_experiment_bound {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ]
    (hfin : conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1) ≠ ∞) :
    (∀ᵐ z : C×Sphere d ∂Γ, reciprocalScale (κ z.1) z.2 ≠ ∞) ∧
    Integrable (fun z : C×Sphere d => Real.log (reciprocalScale (κ z.1) z.2).toReal) Γ ∧
    (∫ z : C×Sphere d, Real.log (reciprocalScale (κ z.1) z.2).toReal ∂Γ) ≤
      cauchyTiltConstant-standardGaussianEntropy+
        (conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1)).toReal := by
  apply reciprocalScale_log_bound Γ κ
  intro n
  have h := cauchyMixture_experiment_bound Γ κ hfin (reciprocalCutoff_pos n) (reciprocalCutoff_le_one n)
  linarith



def residualObservation {d r : ℕ} {C : Type*} (z : (C×Sphere d)×Rows r d) :
    (C×(Rows r d×(Fin r→ℝ)))×Sphere d :=
  ((z.1.1,(z.2,label z.2 (z.1.2:Vector d))),z.1.2)

lemma measurable_residualObservation {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (residualObservation (d:=d) (r:=r) (C:=C)) := by
  unfold residualObservation label
  fun_prop

def residualLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) : Measure ((C×(Rows r d×(Fin r→ℝ)))×Sphere d) :=
  (Γ.prod (gaussianRows r d)).map residualObservation

instance residualLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    IsProbabilityMeasure (residualLaw Γ r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_residualObservation.aemeasurable).mpr inferInstance

lemma residualLaw_support {d r : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    ∀ᵐ z ∂residualLaw Γ r, label z.1.2.1 (z.2:Vector d) = z.1.2.2 := by
  apply (ae_map_iff measurable_residualObservation.aemeasurable
    (measurableSet_eq_fun (by unfold label; fun_prop) (by fun_prop))).mpr
  exact ae_of_all _ (fun _ => rfl)

lemma residualPosterior_support {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    ∀ᵐ c ∂(residualLaw Γ r).fst, ∀ᵐ t : Sphere d ∂(residualLaw Γ r).condKernel c,
      label c.2.1 (t:Vector d) = c.2.2 := by
  apply Measure.ae_ae_of_ae_compProd (p:=fun z : (C×(Rows r d×(Fin r→ℝ)))×Sphere d => label z.1.2.1 (z.2:Vector d) = z.1.2.2)
  rw [(residualLaw Γ r).disintegrate (residualLaw Γ r).condKernel]
  exact residualLaw_support Γ

lemma reciprocalScale_finite_nonatomicAt {d : ℕ} (μ : Measure (Sphere d)) (s : Sphere d)
    (h : reciprocalScale μ s ≠ ∞) : ∀ᵐ t ∂μ, t ≠ s := by
  have ha := ae_lt_top (show Measurable (fun t : Sphere d => (ENNReal.ofReal (dist s t))⁻¹) by fun_prop) h
  filter_upwards [ha] with t ht
  rintro rfl
  simp at ht

lemma reciprocalScale_finite_eq_real {d : ℕ} (μ : Measure (Sphere d)) (s : Sphere d)
    (h : reciprocalScale μ s ≠ ∞) :
    reciprocalScale μ s = ∫⁻ t, ENNReal.ofReal (‖(t:Vector d)-(s:Vector d)‖⁻¹) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [reciprocalScale_finite_nonatomicAt μ s h] with t ht
  have hn : 0 < ‖(t:Vector d)-(s:Vector d)‖ := norm_pos_iff.mpr
    (sub_ne_zero.mpr (fun he => ht (Subtype.ext he)))
  rw [ENNReal.ofReal_inv_of_pos hn]
  congr 2
  change dist (s:Vector d) (t:Vector d) = _
  rw [dist_comm,dist_eq_norm]

lemma label_eq_difference_orthogonal {d r : ℕ} (A : Rows r d) (s t : Vector d)
    (h : label A t = label A s) : t-s ∈ (rowSpan A)ᗮ := by
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro u hu
  induction hu using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨i,rfl⟩ := hv
      rw [inner_sub_left,sub_eq_zero]
      exact congrFun h i
  | zero => simp
  | add x y hx hy hx' hy' => simp [inner_add_right,hx',hy']
  | smul a x hx hx' => simp [inner_smul_right,hx']



def fixedTargetPosterior {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (c : C) (s : Sphere d) :
    Kernel (Rows r d) (Vector d) :=
  ((residualLaw Γ r).condKernel.comap (fun A => (c,(A,label A (s:Vector d))))
    (by unfold label; fun_prop)).map Subtype.val

instance fixedTargetPosterior_markov {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (c : C) (s : Sphere d) :
    IsMarkovKernel (fixedTargetPosterior (r:=r) Γ c s) := by
  unfold fixedTargetPosterior
  exact Kernel.IsMarkovKernel.map _ measurable_subtype_coe

lemma fixedTargetPosterior_support {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (hfin : ∀ᵐ z ∂residualLaw Γ r, reciprocalScale ((residualLaw Γ r).condKernel z.1) z.2 ≠ ∞) :
    ∀ᵐ z : C×Sphere d ∂Γ, ∀ᵐ w ∂(gaussianRows r d) ⊗ₘ fixedTargetPosterior Γ z.1 z.2,
      w.2-(z.2:Vector d) ≠ 0 ∧ w.2-(z.2:Vector d) ∈ (rowSpan w.1)ᗮ := by
  have hs := ae_of_ae_map measurable_residualObservation.aemeasurable
    (ae_of_ae_map measurable_fst.aemeasurable (residualPosterior_support Γ (r:=r)))
  have hf := ae_of_ae_map measurable_residualObservation.aemeasurable hfin
  filter_upwards [Measure.ae_ae_of_ae_prod hs,Measure.ae_ae_of_ae_prod hf] with z hzs hzf
  apply Measure.ae_compProd_of_ae_ae
  · have hm : Measurable (fun w : Rows r d×Vector d => label w.1 (w.2-(z.2:Vector d))) := by
      unfold label
      fun_prop
    have he : {w : Rows r d×Vector d | w.2-(z.2:Vector d) ≠ 0 ∧
        w.2-(z.2:Vector d) ∈ (rowSpan w.1)ᗮ} =
        {w | w.2-(z.2:Vector d) ≠ 0 ∧ label w.1 (w.2-(z.2:Vector d)) = 0} := by
      ext w
      simp only [Set.mem_ofPred_eq,and_congr_right_iff]
      intro _
      constructor
      · intro h
        funext i
        exact Submodule.inner_left_of_mem_orthogonal
          (show w.1 i ∈ rowSpan w.1 from Submodule.subset_span ⟨i,rfl⟩) h
      · intro h
        have he : label w.1 w.2 = label w.1 (z.2:Vector d) := by
          funext i
          have hi := congrFun h i
          simp only [label,inner_sub_left,Pi.zero_apply] at hi
          exact sub_eq_zero.mp hi
        exact label_eq_difference_orthogonal _ _ _ he
    rw [he]
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl.inter
      (measurableSet_eq_fun hm measurable_const)
  · filter_upwards [hzs,hzf] with A hAs hAf
    unfold fixedTargetPosterior
    rw [Kernel.map_apply _ measurable_subtype_coe]
    change ∀ᵐ t ∂(((residualLaw Γ r).condKernel (z.1,(A,label A (z.2:Vector d)))).map Subtype.val),
      t-(z.2:Vector d) ≠ 0 ∧ t-(z.2:Vector d) ∈ (rowSpan A)ᗮ
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      ((measurableSet_eq_fun (by fun_prop) measurable_const).compl.inter
        ((Submodule.isClosed_orthogonal (rowSpan A)).measurableSet.preimage (by fun_prop)))).mpr
    filter_upwards [hAs,reciprocalScale_finite_nonatomicAt _ _ hAf] with t ht hne
    exact ⟨sub_ne_zero.mpr (fun h => hne (Subtype.ext h)),label_eq_difference_orthogonal A _ _ ht⟩



lemma mixed_entropy_log_bound_ae {A X Z : Type*} [MeasurableSpace A] [MeasurableSpace X]
    [MeasurableSpace Z] (P : Measure (A×X)) [IsProbabilityMeasure P]
    (γ : Measure X) (η : Measure Z) [IsProbabilityMeasure γ] [IsProbabilityMeasure η]
    (hKL : klDiv P (P.fst.prod γ) ≠ ∞)
    (K : (A×X)×Z → ℝ≥0∞) (hKm : Measurable K) (hKt : ∀ z, K z ≠ ∞)
    (hKint : ∀ ax, ∫⁻ z, K (ax,z) ∂η ≠ ∞)
    (C : A → ℝ) (hCm : Measurable C) (hC0 : ∀ a, 0 ≤ C a)
    (hCI : Integrable (fun a => Real.log (1+C a)) P.fst)
    {q : ℕ} (hq : 1 ≤ q)
    (hMoment : ∀ᵐ a ∂P.fst, ∫⁻ x, (∫⁻ z, K ((a,x),z) ∂η)^q ∂γ ≤ (ENNReal.ofReal (C a))^q) :
    ∫⁻ axz, ENNReal.ofReal (Real.log (1+(K axz).toReal)) ∂P.prod η ≤
      ENNReal.ofReal ((klDiv P (P.fst.prod γ)).toReal / q +
        ∫ a, Real.log (1+C a) ∂P.fst) := by
  let F : A×X → ℝ≥0∞ := fun ax => ∫⁻ z, K (ax,z) ∂η
  have hFm : Measurable F := Measurable.lintegral_prod_right (f:=fun ax z => K (ax,z)) hKm
  have hf : Measurable (fun ax : A×X => (q:ℝ)*Real.log (1+(F ax).toReal)) :=
    measurable_const.mul (measurable_log_one_add hFm)
  have hc : Measurable (fun ax : A×X => (q:ℝ)*Real.log (1+C ax.1)) :=
    measurable_const.mul ((measurable_const.add (hCm.comp measurable_fst)).log)
  have hCc : Integrable (fun ax : A×X => Real.log (1+C ax.1)) P :=
    (integrable_map_measure (measurable_const.add hCm |>.log.aestronglyMeasurable)
      measurable_fst.aemeasurable).mp hCI
  have hcI := hCc.const_mul (q:ℝ)
  have hExp : ∫⁻ ax : A×X, ENNReal.ofReal (Real.exp
      ((q:ℝ)*Real.log (1+(F ax).toReal)-(q:ℝ)*Real.log (1+C ax.1))) ∂P.fst.prod γ ≤ 1 := by
    rw [lintegral_prod (fun ax : A×X => ENNReal.ofReal (Real.exp
      ((q:ℝ)*Real.log (1+(F ax).toReal)-(q:ℝ)*Real.log (1+C ax.1))))
      (by exact (hf.sub hc).exp.ennreal_ofReal.aemeasurable)]
    calc
      _ ≤ ∫⁻ _a, (1:ℝ≥0∞) ∂P.fst := by
        apply lintegral_mono_ae
        filter_upwards [hMoment] with a hMa
        have heq : (fun x => ENNReal.ofReal (Real.exp
            ((q:ℝ)*Real.log (1+(F (a,x)).toReal)-(q:ℝ)*Real.log (1+C a)))) =
            (fun x => (1+F (a,x))^q / (ENNReal.ofReal (1+C a))^q) := by
          funext x
          exact exp_log_normalization _ (hKint (a,x)) _ (hC0 a) q
        change (∫⁻ x, ENNReal.ofReal (Real.exp
          ((q:ℝ)*Real.log (1+(F (a,x)).toReal)-(q:ℝ)*Real.log (1+C a))) ∂γ) ≤ 1
        rw [heq]
        simp_rw [div_eq_mul_inv]
        have hpow : Measurable (fun x : X => (1+F (a,x))^q) :=
          (measurable_const.add (hFm.comp (measurable_const.prodMk measurable_id))).pow_const q
        rw [lintegral_mul_const _ hpow]
        have hh := lintegral_one_add_pow_le γ (fun x => F (a,x))
          (hFm.comp (measurable_const.prodMk measurable_id)) hq hMa
        have he : ENNReal.ofReal (1+C a) = 1+ENNReal.ofReal (C a) := by
          rw [ENNReal.ofReal_add (by norm_num) (hC0 a), ENNReal.ofReal_one]
        rw [he]
        apply (mul_le_mul' hh le_rfl).trans_eq
        exact ENNReal.mul_inv_cancel (by positivity) (by finiteness)
      _ = 1 := by simp
  obtain ⟨hfi, hbi⟩ := entropy_exp_bound P (P.fst.prod γ) hKL _ _ hf hc
    (fun ax => mul_nonneg (Nat.cast_nonneg _) (log_one_add_nonneg _)) hcI hExp
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqne := hqpos.ne'
  have hLi : Integrable (fun ax => Real.log (1+(F ax).toReal)) P := by
    have hh := hfi.div_const (q:ℝ)
    simpa only [mul_div_cancel_left₀ _ hqne] using hh
  have hCeq : ∫ ax : A×X, Real.log (1+C ax.1) ∂P = ∫ a, Real.log (1+C a) ∂P.fst := by
    exact (integral_map measurable_fst.aemeasurable
      (measurable_const.add hCm |>.log.aestronglyMeasurable)).symm
  rw [integral_const_mul, integral_const_mul, hCeq] at hbi
  have hfinal : ∫ ax, Real.log (1+(F ax).toReal) ∂P ≤
      (klDiv P (P.fst.prod γ)).toReal / q + ∫ a, Real.log (1+C a) ∂P.fst := by
    rw [← sub_le_iff_le_add, le_div_iff₀ hqpos]
    nlinarith
  calc
    _ = ∫⁻ ax, ∫⁻ z, ENNReal.ofReal (Real.log (1+(K (ax,z)).toReal)) ∂η ∂P :=
      lintegral_prod _ (measurable_log_one_add hKm |>.ennreal_ofReal.aemeasurable)
    _ ≤ ∫⁻ ax, ENNReal.ofReal (Real.log (1+(F ax).toReal)) ∂P := by
      exact lintegral_mono fun ax => log_one_add_jensen η (fun z => K (ax,z))
        (hKm.comp (measurable_const.prodMk measurable_id)) (fun z => hKt (ax,z)) (hKint ax)
    _ = ENNReal.ofReal (∫ ax, Real.log (1+(F ax).toReal) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hLi (Filter.Eventually.of_forall fun _ => log_one_add_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal



def residualScale {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (z : C×Sphere d) (A : Rows r d) : ℝ≥0∞ :=
  reciprocalScale ((residualLaw Γ r).condKernel (z.1,(A,label A (z.2:Vector d)))) z.2

lemma measurable_residualScale {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    Measurable (fun z : (C×Sphere d)×Rows r d => residualScale Γ z.1 z.2) := by
  exact (reciprocalScale_kernel_measurable (residualLaw Γ r).condKernel).comp
    measurable_residualObservation

lemma residualScale_lower {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (z : C×Sphere d) (A : Rows r d) :
    ENNReal.ofReal (1/2:ℝ) ≤ residualScale Γ z A := reciprocalScale_lower _ _

lemma fixedTargetPosterior_scale {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (z : C×Sphere d) (A : Rows r d)
    (hf : residualScale Γ z A ≠ ∞) :
    reciprocalKernelScale (fixedTargetPosterior Γ z.1 z.2) (z.2:Vector d) A = residualScale Γ z A := by
  unfold reciprocalKernelScale fixedTargetPosterior
  rw [Kernel.map_apply _ measurable_subtype_coe]
  rw [lintegral_map (by fun_prop) measurable_subtype_coe]
  exact (reciprocalScale_finite_eq_real _ _ hf).symm

def residualCube {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (δ : ℝ)
    (w : ((C×Sphere d)×Vector d)×Rows r d) : ℝ≥0∞ :=
  (∫⁻ t : Sphere d, cubeKernel δ ⟪(t:Vector d)-(w.1.1.2:Vector d),w.1.2⟫
    ∂(residualLaw Γ r).condKernel (w.1.1.1,(w.2,label w.2 (w.1.1.2:Vector d)))) /
      residualScale Γ w.1.1 w.2

lemma measurable_residualCube {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (δ : ℝ) :
    Measurable (residualCube (r:=r) Γ δ) := by
  let f : ((C×Sphere d)×Vector d)×Rows r d → C×(Rows r d×(Fin r→ℝ)) :=
    fun w => (w.1.1.1,(w.2,label w.2 (w.1.1.2:Vector d)))
  have hf : Measurable f := by unfold f label; fun_prop
  have hn : Measurable (fun w : ((C×Sphere d)×Vector d)×Rows r d =>
      ∫⁻ t : Sphere d, cubeKernel δ ⟪(t:Vector d)-(w.1.1.2:Vector d),w.1.2⟫
      ∂(residualLaw Γ r).condKernel (f w)) :=
    (show Measurable (fun z : (((C×Sphere d)×Vector d)×Rows r d)×Sphere d =>
      cubeKernel δ ⟪(z.2:Vector d)-(z.1.1.1.2:Vector d),z.1.1.2⟫) from
      (measurable_cubeKernel δ).comp (by fun_prop)).lintegral_kernel_prod_right
      (f:=fun w t => cubeKernel δ ⟪(t:Vector d)-(w.1.1.2:Vector d),w.1.2⟫)
      (κ:=(residualLaw Γ r).condKernel.comap f hf)
  exact hn.div ((measurable_residualScale Γ).comp
    (measurable_fst.fst.prodMk measurable_snd))

lemma residualCube_bound {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (δ : ℝ)
    (w : ((C×Sphere d)×Vector d)×Rows r d) :
    residualCube Γ δ w ≤ ENNReal.ofReal ((2*δ)⁻¹) * 2 := by
  have hn : (∫⁻ t : Sphere d, cubeKernel δ ⟪(t:Vector d)-(w.1.1.2:Vector d),w.1.2⟫
      ∂(residualLaw Γ r).condKernel (w.1.1.1,(w.2,label w.2 (w.1.1.2:Vector d)))) ≤
      ENNReal.ofReal ((2*δ)⁻¹) := by
    calc
      _ ≤ ∫⁻ _t : Sphere d, ENNReal.ofReal ((2*δ)⁻¹)
          ∂(residualLaw Γ r).condKernel (w.1.1.1,(w.2,label w.2 (w.1.1.2:Vector d))) :=
        lintegral_mono (fun t => by
          unfold cubeKernel
          exact Set.indicator_le_self _ _ _)
      _ = _ := by simp
  have ha : (residualScale Γ w.1.1 w.2)⁻¹ ≤ (2:ℝ≥0∞) := by
    have h := ENNReal.inv_le_inv.mpr (residualScale_lower Γ w.1.1 w.2)
    have he : (ENNReal.ofReal (1/2:ℝ))⁻¹ = (2:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_one,ENNReal.ofReal_ofNat]
      simp
    rwa [he] at h
  exact mul_le_mul' hn ha

lemma residualCube_finite {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (δ : ℝ)
    (w : ((C×Sphere d)×Vector d)×Rows r d) : residualCube Γ δ w ≠ ∞ :=
  ne_top_of_le_ne_top (by finiteness) (residualCube_bound Γ δ w)

lemma residualCube_integral_finite {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (δ : ℝ)
    (w : (C×Sphere d)×Vector d) :
    (∫⁻ A, residualCube Γ δ (w,A) ∂gaussianRows r d) ≠ ∞ := by
  apply ne_top_of_le_ne_top (b:=ENNReal.ofReal ((2*δ)⁻¹)*2) (by finiteness)
  exact (lintegral_mono (fun A => residualCube_bound Γ δ (w,A))).trans_eq (by simp)

lemma residualCube_moment {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (hfin : ∀ᵐ z ∂residualLaw Γ r, reciprocalScale ((residualLaw Γ r).condKernel z.1) z.2 ≠ ∞)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ z : C×Sphere d ∂Γ, ∫⁻ x, (∫⁻ A, residualCube Γ δ ((z,x),A)
      ∂gaussianRows r d)^q ∂stdGaussian (Vector d) ≤ ENNReal.ofReal (5*kernelSmallBallConstant)^q := by
  have hdpos : 0 < d := by omega
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hdpos
  have hf := Measure.ae_ae_of_ae_prod (ae_of_ae_map measurable_residualObservation.aemeasurable hfin)
  filter_upwards [fixedTargetPosterior_support Γ hfin,hf] with z hzs hzf
  have heq : ∀ᵐ A ∂gaussianRows r d,
      reciprocalKernelScale (fixedTargetPosterior Γ z.1 z.2) (z.2:Vector d) A = residualScale Γ z A := by
    filter_upwards [hzf] with A hA
    exact fixedTargetPosterior_scale Γ z A hA
  have hscale : ∀ᵐ A ∂gaussianRows r d,
      reciprocalKernelScale (fixedTargetPosterior Γ z.1 z.2) (z.2:Vector d) A ≠ 0 ∧
      reciprocalKernelScale (fixedTargetPosterior Γ z.1 z.2) (z.2:Vector d) A ≠ ∞ := by
    filter_upwards [heq,hzf] with A he hf
    rw [he]
    exact ⟨ne_of_gt (lt_of_lt_of_le (by norm_num) (residualScale_lower Γ z A)),hf⟩
  have h := reciprocal_kernel_projection_moment (E:=Vector d)
    (by simpa) (by simpa) hq hmargin (fixedTargetPosterior Γ z.1 z.2) (z.2:Vector d)
    hscale hzs (cubeKernel δ) (measurable_cubeKernel δ) (lintegral_cubeKernel hδ)
  apply le_trans (le_of_eq ?_) h
  apply lintegral_congr
  intro x
  congr 1
  apply lintegral_congr_ae
  filter_upwards [heq] with A he
  rw [he]
  unfold residualCube fixedTargetPosterior
  rw [Kernel.map_apply _ measurable_subtype_coe,lintegral_map
    (f:=fun t : Vector d => cubeKernel δ ⟪t-(z.2:Vector d),x⟫)
    ((measurable_cubeKernel δ).comp (by fun_prop)) measurable_subtype_coe]
  rfl




def scalarCube (μ : Measure ℝ) (y δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, cubeKernel δ (t-y) ∂μ

lemma scalarCube_ball (μ : Measure ℝ) (y : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    scalarCube μ y δ = μ (Metric.closedBall y δ) / volume (Metric.closedBall y δ) := by
  have he : (fun t : ℝ => cubeKernel δ (t-y)) =
      Set.indicator (Metric.closedBall y δ) (fun _ => ENNReal.ofReal ((2*δ)⁻¹)) := by
    ext t
    simp only [cubeKernel,Set.indicator_apply]
    congr 1
    simp only [Set.mem_Icc,Metric.mem_closedBall,Real.dist_eq,abs_le]
  unfold scalarCube
  rw [he,lintegral_indicator Metric.isClosed_closedBall.measurableSet,
    lintegral_const,Measure.restrict_apply_univ,Real.volume_closedBall,
    ENNReal.ofReal_inv_of_pos (by positivity),div_eq_mul_inv,mul_comm]

lemma measurable_scalarCube {A : Type*} [MeasurableSpace A]
    (κ : Kernel A ℝ) [IsSFiniteKernel κ] (δ : ℝ) :
    Measurable (fun z : A×ℝ => scalarCube (κ z.1) z.2 δ) := by
  exact ((measurable_cubeKernel δ).comp (show Measurable (fun z : (A×ℝ)×ℝ => z.2-z.1.2) by fun_prop)).lintegral_kernel_prod_right
    (f:=fun z t => cubeKernel δ (t-z.2)) (κ:=κ.comap Prod.fst measurable_fst)

def scalarExtended (μ : Measure ℝ) (y : ℝ) : ℝ≥0∞ :=
  liminf (fun n : ℕ => scalarCube μ y (1/(n:ℝ))) atTop

def scalarDensity (μ : Measure ℝ) (y : ℝ) : ℝ≥0∞ :=
  if scalarExtended μ y = ∞ then 0 else scalarExtended μ y

lemma measurable_scalarExtended {A : Type*} [MeasurableSpace A]
    (κ : Kernel A ℝ) [IsSFiniteKernel κ] :
    Measurable (fun z : A×ℝ => scalarExtended (κ z.1) z.2) :=
  Measurable.liminf (fun n => measurable_scalarCube κ (1/(n:ℝ)))

lemma measurable_scalarDensity {A : Type*} [MeasurableSpace A]
    (κ : Kernel A ℝ) [IsSFiniteKernel κ] :
    Measurable (fun z : A×ℝ => scalarDensity (κ z.1) z.2) := by
  exact Measurable.ite (measurableSet_eq_fun (measurable_scalarExtended κ) measurable_const)
    measurable_const (measurable_scalarExtended κ)

lemma scalarDensity_finite (μ : Measure ℝ) (y : ℝ) : scalarDensity μ y ≠ ∞ := by
  unfold scalarDensity
  split_ifs with h <;> simp_all

lemma scalarDensity_ae_rnDeriv (μ : Measure ℝ) [IsFiniteMeasure μ] :
    scalarDensity μ =ᵐ[volume] μ.rnDeriv volume := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ volume,Measure.rnDeriv_ne_top μ volume] with y hy hyt
  have ht := hy.comp tendsto_cube_scale
  have he : (fun n : ℕ => scalarCube μ y (1/(n:ℝ))) =ᶠ[atTop]
      fun n : ℕ => μ (Metric.closedBall y (1/(n:ℝ))) / volume (Metric.closedBall y (1/(n:ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact scalarCube_ball μ y (by positivity)
  have hl : scalarExtended μ y = μ.rnDeriv volume y := (ht.congr' he.symm).liminf_eq
  simp only [scalarDensity,hl,ite_eq_right hyt]

lemma scalarDensity_ae_limit (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ y ∂(volume : Measure ℝ), Tendsto (fun n : ℕ => scalarCube μ y (1/(n:ℝ)))
      atTop (𝓝 (scalarDensity μ y)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ volume,scalarDensity_ae_rnDeriv μ] with y hy heq
  have he : (fun n : ℕ => scalarCube μ y (1/(n:ℝ))) =ᶠ[atTop]
      fun n : ℕ => μ (Metric.closedBall y (1/(n:ℝ))) / volume (Metric.closedBall y (1/(n:ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact scalarCube_ball μ y (by positivity)
  rw [heq]
  exact (hy.comp tendsto_cube_scale).congr' he.symm

lemma scalarDensity_withDensity (μ : Measure ℝ) [IsFiniteMeasure μ] (h : μ ≪ volume) :
    volume.withDensity (scalarDensity μ) = μ := by
  rw [withDensity_congr_ae (scalarDensity_ae_rnDeriv μ)]
  exact Measure.withDensity_rnDeriv_eq _ _ h

lemma kernel_scalarDensity_withDensity {A : Type*} [MeasurableSpace A]
    (π : Measure A) [SFinite π] (κ : Kernel A ℝ) [IsFiniteKernel κ]
    (h : ∀ᵐ a ∂π, κ a ≪ volume) :
    (π.prod volume).withDensity (fun z : A×ℝ => scalarDensity (κ z.1) z.2) = π ⊗ₘ κ := by
  apply Measure.ext
  intro t ht
  rw [withDensity_apply _ ht,←lintegral_indicator ht,
    lintegral_prod _ ((measurable_scalarDensity κ).indicator ht).aemeasurable,
    Measure.compProd_apply ht]
  apply lintegral_congr_ae
  filter_upwards [h] with a ha
  have ht' : MeasurableSet (Prod.mk a ⁻¹' t) := ht.preimage (measurable_const.prodMk measurable_id)
  rw [←scalarDensity_withDensity (κ a) ha,withDensity_apply _ ht',←lintegral_indicator ht']
  rfl

lemma kernel_scalarDensity_ae_limit {A : Type*} [MeasurableSpace A]
    (π : Measure A) [SFinite π] (κ : Kernel A ℝ) [IsFiniteKernel κ] :
    ∀ᵐ z : A×ℝ ∂π.prod volume, Tendsto
      (fun n : ℕ => scalarCube (κ z.1) z.2 (1/(n:ℝ))) atTop (𝓝 (scalarDensity (κ z.1) z.2)) := by
  have hm : MeasurableSet {z : A×ℝ | Tendsto
      (fun n : ℕ => scalarCube (κ z.1) z.2 (1/(n:ℝ))) atTop (𝓝 (scalarDensity (κ z.1) z.2))} :=
    measurableSet_tendsto_fun (fun n : ℕ => measurable_scalarCube κ (1/(n:ℝ))) (measurable_scalarDensity κ)
  exact (Measure.ae_prod_iff_ae_ae hm).mpr (ae_of_all _ (fun a => scalarDensity_ae_limit (κ a)))



end CurrentProjection

end

end OAI
