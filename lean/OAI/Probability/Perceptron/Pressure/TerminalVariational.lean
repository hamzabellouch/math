import Mathlib
import OAI.Probability.Perceptron.Control.ControlDrift

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def terminalVariational (P : Measure BrownianPath) (α : ℝ) (f : ℝ →ᵇ ℝ) : EReal :=
  ⨅ m : Trial, ((α * controlValue P f m : ℝ) : EReal) + (entropy m).toEReal

lemma variationalValue_eq_terminal (P : Measure BrownianPath) (α β : ℝ) (φ : ℝ →ᵇ ℝ) :
    variationalValue P α β φ = terminalVariational P α (β • φ) := rfl

lemma terminalVariational_bounds (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) :
    ((-α*‖f‖ : ℝ) : EReal) ≤ terminalVariational P α f ∧
      terminalVariational P α f ≤ ((α*‖f‖ : ℝ) : EReal) := by
  constructor
  · apply le_iInf
    intro m
    have hcv : -α*‖f‖ ≤ α*controlValue P f m := by
      nlinarith [mul_le_mul_of_nonneg_left (neg_norm_le_controlValue P f m) hα]
    exact (EReal.coe_le_coe_iff.mpr hcv).trans
      (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _))
  · calc
      _ ≤ ((α*controlValue P f oneTrial : ℝ) : EReal) + (entropy oneTrial).toEReal :=
        iInf_le _ oneTrial
      _ ≤ ((α*‖f‖ : ℝ) : EReal) := by
        simp only [entropy_oneTrial, EReal.coe_ennreal_zero, add_zero]
        exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left (controlValue_le_norm P f _) hα)

lemma terminalVariational_coe_toReal (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) :
    ((terminalVariational P α f).toReal : EReal) = terminalVariational P α f := by
  obtain ⟨hlo,hhi⟩ := terminalVariational_bounds P α hα f
  exact EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo)

lemma terminalVariational_toReal_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f g : ℝ →ᵇ ℝ) (δ : ℝ)
    (hfg : ∀ m : Trial, controlValue P f m - controlValue P g m ≤ δ) :
    (terminalVariational P α f).toReal - (terminalVariational P α g).toReal ≤ α*δ := by
  have hbound : (((terminalVariational P α f).toReal - α*δ : ℝ) : EReal) ≤
      terminalVariational P α g := by
    apply le_iInf
    intro m
    have h : terminalVariational P α f ≤
        ((α*controlValue P f m : ℝ) : EReal) + (entropy m).toEReal := iInf_le _ m
    have hh : (((terminalVariational P α f).toReal - α*δ : ℝ) : EReal) ≤
        ((α*controlValue P f m - α*δ : ℝ) : EReal) + (entropy m).toEReal := by
      have hs := add_le_add_right h ((-α*δ : ℝ) : EReal)
      rw [← terminalVariational_coe_toReal P α hα f] at hs
      convert hs using 1 <;> simp only [sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] <;>
        push_cast <;> simp only [neg_mul, add_assoc, add_comm]
    apply hh.trans
    apply add_le_add_left
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hfg m) hα]
  rw [← terminalVariational_coe_toReal P α hα g, EReal.coe_le_coe_iff] at hbound
  linarith

lemma terminalVariational_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f g : ℝ →ᵇ ℝ) (δ : ℝ)
    (hfg : ∀ m : Trial, |controlValue P f m - controlValue P g m| ≤ δ) :
    |(terminalVariational P α f).toReal - (terminalVariational P α g).toReal| ≤ α*δ := by
  have h₁ := terminalVariational_toReal_sub_le P α hα f g δ
    (fun m => (abs_le.mp (hfg m)).2)
  have h₂ := terminalVariational_toReal_sub_le P α hα g f δ
    (fun m => by have hh := (abs_le.mp (hfg m)).1; linarith)
  exact abs_le.mpr ⟨by linarith, h₁⟩

lemma indep_eventuallyMeasurable_left {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) {m n : MeasurableSpace Ω} (h : Indep m n μ) :
    Indep (eventuallyMeasurableSpace m (ae μ)) n μ := by
  rw [Indep_iff] at h ⊢
  rintro A B ⟨A', hA', hAA'⟩ hB
  rw [measure_congr (hAA'.inter (Filter.EventuallyEq.refl (ae μ) B)), measure_congr hAA']
  exact h A' B hA' hB

lemma nullSigma_le_eventuallyMeasurable (P : Measure BrownianPath)
    (m : MeasurableSpace BrownianPath) :
    nullSigma P ≤ eventuallyMeasurableSpace m (ae P) := by
  apply MeasurableSpace.generateFrom_le
  intro A hA
  exact ⟨∅, MeasurableSet.empty, ae_eq_empty.mpr hA⟩

@[instance_reducible] def rawBrownianSigma (s : ℝ≥0) : MeasurableSpace BrownianPath :=
  ⨆ r : {r : ℝ≥0 // r ≤ s},
    MeasurableSpace.comap (brownianEval r.val) (borel ℝ)

lemma rawBrownianSigma_le (s : ℝ≥0) : rawBrownianSigma s ≤ (inferInstance : MeasurableSpace BrownianPath) := by
  apply iSup_le
  intro r
  exact (brownianEval_measurable r.val).comap_le

lemma rawBrownianSigma_le_past_comap (s : ℝ≥0) :
    rawBrownianSigma s ≤
      MeasurableSpace.comap (fun ω (r : Set.Iic s) => brownianEval r.val ω) inferInstance := by
  apply iSup_le
  intro r
  rintro A ⟨B, hB, rfl⟩
  exact ⟨(fun f : Set.Iic s → ℝ => f r) ⁻¹' B, (measurable_pi_apply r) hB, rfl⟩

lemma usualBrownianSigma_le_ae_raw (P : Measure BrownianPath) (t : Time)
    (s : ℝ≥0) (hts : (t : ℝ) < s) :
    usualBrownianSigma P t ≤ eventuallyMeasurableSpace (rawBrownianSigma s) (ae P) := by
  apply (iInf_le _ (⟨s, hts⟩ : {s : ℝ≥0 // (t : ℝ) < s})).trans
  exact sup_le le_eventuallyMeasurableSpace (nullSigma_le_eventuallyMeasurable P _)

lemma brownian_future_indep_raw (P : Measure BrownianPath)
    (hB : IsBrownianReal brownianEval P) (s u : ℝ≥0) :
    Indep (rawBrownianSigma s)
      (MeasurableSpace.comap (fun ω => brownianEval (s+u) ω - brownianEval s ω) (borel ℝ)) P := by
  have h := (hB.toIsPreBrownianReal.indepFun_shift s).symm.comp
    measurable_id (measurable_pi_apply u)
  exact indep_of_indep_of_le_left h (rawBrownianSigma_le_past_comap s)

lemma brownian_future_indep_usual_earlier (P : Measure BrownianPath)
    (hB : IsBrownianReal brownianEval P) (t : Time) (s u : ℝ≥0)
    (hts : (t : ℝ) < s) :
    Indep (usualBrownianSigma P t)
      (MeasurableSpace.comap (fun ω => brownianEval (s+u) ω - brownianEval s ω) (borel ℝ)) P :=
  indep_of_indep_of_le_left
    (indep_eventuallyMeasurable_left P (brownian_future_indep_raw P hB s u))
    (usualBrownianSigma_le_ae_raw P t s hts)

lemma indep_setIntegral_eq_mul_null {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) {X : Ω → ℝ} {A : Set Ω}
    (hI : Indep m (MeasurableSpace.comap X (borel ℝ)) P)
    (hX : AEMeasurable X P) (hA : MeasurableSet[m] A) (hAn : NullMeasurableSet A P)
    (f : ℝ →ᵇ ℝ) :
    (∫ ω in A, f (X ω) ∂P) = P.real A * ∫ ω, f (X ω) ∂P := by
  calc
    _ = ∫ ω, id (A.indicator (1 : Ω → ℝ) ω) * f (X ω) ∂P := by
      rw [← integral_indicator₀ hAn]
      congr with ω
      by_cases hω : ω ∈ A <;> simp [hω]
    _ = _ := by
      simp only [Pi.one_def]
      rw [IndepFun.integral_fun_comp_mul_comp
        (hI.indicator_indepFun 1 hA)
        ((aemeasurable_indicator_const_iff 1).2 hAn) hX
        measurable_id.aestronglyMeasurable f.continuous.measurable.aestronglyMeasurable]
      simp only [id_eq, integral_indicator₀ hAn, integral_const, smul_eq_mul, mul_one,
        measureReal_def, Measure.restrict_apply_univ]

lemma indep_comap_of_ae_tendsto {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : ∀ A, MeasurableSet[m] A → NullMeasurableSet A P)
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hI : ∀ n, Indep m (MeasurableSpace.comap (X n) (borel ℝ)) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Indep m (MeasurableSpace.comap Y (borel ℝ)) P := by
  apply (Indep_iff_IndepSets _ _ P).2
  apply indepSets_comap_of_bcf (fun A hA => hm A hA) hY
  intro A hA f
  have hall := tendsto_integral_of_dominated_convergence (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _)
    (hlim.mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω)
  have hres := tendsto_integral_of_dominated_convergence (μ := P.restrict A)
    (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable.restrict)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _)
    ((ae_restrict_of_ae hlim).mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω)
  apply tendsto_nhds_unique hres
  convert hall.const_mul (P.real A) using 1
  ext n
  exact indep_setIntegral_eq_mul_null P (hI n) (hX n) hA (hm A hA) f

lemma brownian_increment_indep_usual (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (t : Time) (r : ℝ≥0) (htr : (t : ℝ) < r) :
    Indep (usualBrownianSigma P t)
      (MeasurableSpace.comap (fun ω => brownianEval r ω -
        brownianEval ⟨t.val, t.property.1⟩ ω) (borel ℝ)) P := by
  let t₀ : ℝ≥0 := ⟨t.val, t.property.1⟩
  have ht₀r : t₀ < r := htr
  obtain ⟨s, -, hs, hlim⟩ := exists_seq_strictAnti_tendsto' ht₀r
  apply indep_comap_of_ae_tendsto P (fun A hA =>
    (usualBrownianSigma_le_completion P t A hA))
    (X := fun n ω => brownianEval r ω - brownianEval (s n) ω)
    (fun n => ((brownianEval_measurable r).sub (brownianEval_measurable (s n))).aemeasurable)
    (((brownianEval_measurable r).sub (brownianEval_measurable t₀)).aemeasurable)
  · intro n
    have hI := brownian_future_indep_usual_earlier P hB t (s n) (r-s n) (hs n).1
    rwa [add_tsub_cancel_of_le (hs n).2.le] at hI
  · exact Filter.Eventually.of_forall fun ω => tendsto_const_nhds.sub
      (ω.continuous.continuousAt.tendsto.comp hlim)

def clipControl (L : ℝ) (v : Time → BrownianPath → ℝ) : Time → BrownianPath → ℝ :=
  fun t ω => max (-L) (min L (v t ω))

lemma progressive_clipControl (P : Measure BrownianPath) {v : Time → BrownianPath → ℝ}
    (hv : Progressive P v) (L : ℝ) : Progressive P (clipControl L v) := by
  intro t
  exact measurable_const.max (measurable_const.min (hv t))

lemma abs_clip_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) : |max (-L) (min L x)| ≤ L := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma clip_cost_gain {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    L * |x - max (-L) (min L x)| ≤ (x^2 - (max (-L) (min L x))^2)/2 := by
  by_cases hx : x ≤ -L
  · have hxL : x ≤ L := hx.trans (by linarith)
    rw [min_eq_right hxL, max_eq_left hx, abs_of_nonpos (by linarith)]
    nlinarith [sq_nonneg (x+L)]
  · by_cases hLx : L ≤ x
    · rw [min_eq_left hLx, max_eq_right (by linarith : -L ≤ L),
        abs_of_nonneg (by linarith : 0 ≤ x-L)]
      nlinarith [sq_nonneg (x-L)]
    · rw [min_eq_right (le_of_not_ge hLx), max_eq_right (le_of_not_ge hx)]
      simp

lemma clip_sq_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    (max (-L) (min L x))^2 ≤ x^2 := by
  have h := clip_cost_gain hL x
  nlinarith [mul_nonneg hL (abs_nonneg (x - max (-L) (min L x)))]

lemma pathControlCost_clip_le (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) (ω : BrownianPath) :
    pathControlCost m (clipControl L v) ω ≤ pathControlCost m v ω := by
  apply lintegral_mono
  intro t
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (clip_sq_le hL _) (m.nonneg t))

lemma controlCost_clip_le (P : Measure BrownianPath) (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) : controlCost P m (clipControl L v) ≤ controlCost P m v :=
  lintegral_mono fun ω => pathControlCost_clip_le m hL v ω

lemma weightedTime_integrable (m : Trial) {v : Time → ℝ} (hv : Measurable v)
    (hc : (∫⁻ t, ENNReal.ofReal (m t * v t ^ 2) ∂timeLaw) < ∞) :
    Integrable (fun t => m t * v t ^ 2) timeLaw ∧
      Integrable (fun t => m t * v t) timeLaw := by
  have hm : Integrable m timeLaw :=
    (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simpa [abs_of_nonneg (m.nonneg t)] using m.le_one t)
  have hq : Integrable (fun t => m t * v t ^ 2) timeLaw :=
    ⟨(m.measurable.mul (hv.pow_const 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t =>
        mul_nonneg (m.nonneg t) (sq_nonneg _))).mpr hc⟩
  refine ⟨hq, (hq.add hm).mono' (m.measurable.mul hv).aestronglyMeasurable ?_⟩
  apply Filter.Eventually.of_forall
  intro t
  change |m t * v t| ≤ m t * v t ^ 2 + m t
  rw [abs_mul, abs_of_nonneg (m.nonneg t)]
  have h : |v t| ≤ v t ^ 2 + 1 := by nlinarith [sq_nonneg (|v t| - 1), sq_abs (v t)]
  nlinarith [mul_le_mul_of_nonneg_left h (m.nonneg t)]

lemma integral_pathControlCost (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    (∫ ω, (pathControlCost m v ω).toReal ∂P) = (controlCost P m v).toReal :=
  integral_toReal (pathControlCost_aemeasurable P m hv)
    (ae_lt_top' (pathControlCost_aemeasurable P m hv) hc.ne)

lemma clipping_drift_gain (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    {v : Time → BrownianPath → ℝ} (ω : BrownianPath)
    (hv : Measurable (fun t => v t ω)) (hc : pathControlCost m v ω < ∞) :
    L * |controlDrift m v ω - controlDrift m (clipControl L v) ω| ≤
      ((pathControlCost m v ω).toReal - (pathControlCost m (clipControl L v) ω).toReal)/2 := by
  have hw : Measurable (fun t => clipControl L v t ω) := measurable_const.max (measurable_const.min hv)
  have hcv := weightedTime_integrable m hv hc
  have hcw := weightedTime_integrable m hw ((pathControlCost_clip_le m hL v ω).trans_lt hc)
  have hev : (∫ t, m t * v t ω ^ 2 ∂timeLaw) = (pathControlCost m v ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcv.1.aestronglyMeasurable
  have hew : (∫ t, m t * clipControl L v t ω ^ 2 ∂timeLaw) =
      (pathControlCost m (clipControl L v) ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcw.1.aestronglyMeasurable
  unfold controlDrift
  rw [← integral_sub hcv.2 hcw.2]
  calc
    _ ≤ L * ∫ t, |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hL
    _ = ∫ t, L * |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ t, (m t * v t ω ^ 2 - m t * clipControl L v t ω ^ 2)/2 ∂timeLaw := by
      apply integral_mono ((hcv.2.sub hcw.2).abs.const_mul L) ((hcv.1.sub hcw.1).div_const 2)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← mul_sub, abs_mul, abs_of_nonneg (m.nonneg t)]
      have h := mul_le_mul_of_nonneg_left (clip_cost_gain hL (v t ω)) (m.nonneg t)
      dsimp [clipControl]
      nlinarith
    _ = _ := by rw [integral_div, integral_sub hcv.1 hcw.1, hev, hew]

lemma controlPayoff_le_clipControl (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    controlPayoff P f m v ≤ controlPayoff P f m (clipControl L v) := by
  let w := clipControl L v
  have hw : Progressive P w := progressive_clipControl P hv L
  have hcw : controlCost P m w < ∞ := (controlCost_clip_le P m L.coe_nonneg v).trans_lt hc
  have hpv := pathControlCost_aemeasurable P m hv
  have hpw := pathControlCost_aemeasurable P m hw
  have hcvI := integrable_toReal_of_lintegral_ne_top hpv hc.ne
  have hcwI := integrable_toReal_of_lintegral_ne_top hpw hcw.ne
  have hineq : (∫ ω, (f (brownianEval 1 ω + controlDrift m v ω) -
        f (brownianEval 1 ω + controlDrift m w ω)) ∂P) ≤
      (∫ ω, ((pathControlCost m v ω).toReal - (pathControlCost m w ω).toReal)/2 ∂P) := by
    apply integral_mono_ae ((controlReward_integrable P f m hv).sub (controlReward_integrable P f m hw))
      ((hcvI.sub hcwI).div_const 2)
    filter_upwards [ae_lt_top' hpv hc.ne] with ω hω
    have hLip := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
      (brownianEval 1 ω + controlDrift m w ω)
    rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hLip
    exact (le_abs_self _).trans (hLip.trans
      (clipping_drift_gain m L.coe_nonneg ω (progressive_time_measurable P hv ω) hω))
  rw [integral_sub (controlReward_integrable P f m hv) (controlReward_integrable P f m hw),
    integral_div, integral_sub hcvI hcwI, integral_pathControlCost P m hv hc,
    integral_pathControlCost P m hw hcw] at hineq
  unfold controlPayoff
  change _ ≤ _
  dsimp only [controlDrift, w] at hineq
  linarith

lemma controlValue_le_of_bounded_controls (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) (b : ℝ)
    (hb : ∀ v : Time → BrownianPath → ℝ, Progressive P v → controlCost P m v < ∞ →
      (∀ t ω, |v t ω| ≤ L) → controlPayoff P f m v ≤ b) : controlValue P f m ≤ b := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, hv, hc, rfl⟩
  exact (controlPayoff_le_clipControl P f m L hf hv hc).trans
    (hb (clipControl L v) (progressive_clipControl P hv L)
      ((controlCost_clip_le P m L.coe_nonneg v).trans_lt hc)
      (fun t ω => abs_clip_le L.coe_nonneg (v t ω)))

lemma pathControlCost_le_bound (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath) :
    pathControlCost m v ω ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _t : Time, ENNReal.ofReal ((L : ℝ)^2) ∂timeLaw := by
      apply lintegral_mono
      intro t
      apply ENNReal.ofReal_le_ofReal
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      exact (mul_le_mul_of_nonneg_right (m.le_one t) (sq_nonneg _)).trans (by simpa using hx)
    _ = _ := by simp

lemma controlCost_le_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) :
    controlCost P m v ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _ω : BrownianPath, ENNReal.ofReal ((L : ℝ)^2) ∂P :=
      lintegral_mono fun ω => pathControlCost_le_bound m L hv ω
    _ = _ := by simp

lemma trial_abs_sub_integrable (m n : Trial) :
    Integrable (fun t => |m t - n t|) timeLaw := by
  apply (integrable_const (2 : ℝ)).mono'
    ((m.measurable.sub n.measurable).abs.aestronglyMeasurable)
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_abs]
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg (m.nonneg t), abs_of_nonneg (n.nonneg t)]; linarith [m.le_one t,n.le_one t])

lemma bounded_drift_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |controlDrift m v ω - controlDrift n v ω| ≤ (L : ℝ) * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  rw [controlDrift, controlDrift, ← integral_sub hm.2 hn.2]
  calc
    _ ≤ ∫ t, |m t * v t ω - n t * v t ω| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ) * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.2.sub hn.2).abs ((trial_abs_sub_integrable m n).const_mul L)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hv t ω) (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma bounded_pathCost_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ≤
      (L : ℝ)^2 * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  have hem : (pathControlCost m v ω).toReal = ∫ t, m t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hm.1.aestronglyMeasurable).symm
  have hen : (pathControlCost n v ω).toReal = ∫ t, n t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (n.nonneg t) (sq_nonneg _))
      hn.1.aestronglyMeasurable).symm
  rw [hem, hen, ← integral_sub hm.1 hn.1]
  calc
    _ ≤ ∫ t, |m t * v t ω ^ 2 - n t * v t ω ^ 2| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ)^2 * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.1.sub hn.1).abs ((trial_abs_sub_integrable m n).const_mul ((L : ℝ)^2))
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (v t ω))]
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma controlPayoff_trial_diff_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hbound : ∀ t ω, |v t ω| ≤ L) :
    |controlPayoff P f m v - controlPayoff P f n v| ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  let D := ∫ t, |m t-n t| ∂timeLaw
  have hcm : controlCost P m v < ∞ := (controlCost_le_bound P m L hbound).trans_lt (by finiteness)
  have hcn : controlCost P n v < ∞ := (controlCost_le_bound P n L hbound).trans_lt (by finiteness)
  have hm := controlReward_integrable P f m hv
  have hn := controlReward_integrable P f n hv
  have hrew : |(∫ ω, f (brownianEval 1 ω + controlDrift m v ω) ∂P) -
      (∫ ω, f (brownianEval 1 ω + controlDrift n v ω) ∂P)| ≤ (L : ℝ)^2 * D := by
    rw [← integral_sub hm hn]
    calc
      _ ≤ ∫ ω, |f (brownianEval 1 ω + controlDrift m v ω) -
          f (brownianEval 1 ω + controlDrift n v ω)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono (hm.sub hn).abs (integrable_const _)
        intro ω
        have hh := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
          (brownianEval 1 ω + controlDrift n v ω)
        rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hh
        have hb := mul_le_mul_of_nonneg_left
          (bounded_drift_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)) L.coe_nonneg
        exact hh.trans (by dsimp only [D]; nlinarith [hb])
      _ = _ := by simp
  have hcost : |(controlCost P m v).toReal - (controlCost P n v).toReal| ≤ (L : ℝ)^2 * D := by
    rw [← integral_pathControlCost P m hv hcm, ← integral_pathControlCost P n hv hcn,
      ← integral_sub (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne)
        (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)]
    calc
      _ ≤ ∫ ω, |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono
          ((integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne).sub
            (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)).abs
          (integrable_const _)
        intro ω
        exact bounded_pathCost_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)
      _ = _ := by simp
  apply abs_le.mpr
  obtain ⟨hrewlo,hrewhi⟩ := abs_le.mp hrew
  obtain ⟨hcostlo,hcosthi⟩ := abs_le.mp hcost
  dsimp only [controlPayoff, controlDrift] at *
  constructor <;> linarith

end SphericalPerceptronFreeEnergy
end

end OAI
