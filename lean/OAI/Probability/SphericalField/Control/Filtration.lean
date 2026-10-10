import Mathlib
import OAI.Probability.SphericalField.Perceptron.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma brownianEval_measurable (t : ℝ≥0) : Measurable (brownianEval t) :=
  (continuous_eval_const t).measurable

lemma usualBrownianSigma_le_completion (P : Measure BrownianPath) (t : Time) :
    usualBrownianSigma P t ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace BrownianPath P)) := by
  unfold usualBrownianSigma
  refine (iInf_le _ (⟨2, lt_of_le_of_lt t.property.2 (by norm_num)⟩ :
    {s : ℝ≥0 // (t : ℝ) < s})).trans ?_
  apply sup_le
  · apply iSup_le
    intro r
    exact (brownianEval_measurable r.val).comap_le.trans
      (fun _ hs => hs.nullMeasurableSet)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact NullMeasurableSet.of_null hs

lemma progressive_joint_complete (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    Measurable (fun p : Time × NullMeasurableSpace BrownianPath P => v p.1 p.2) := by
  have h := (hv 1).mono (show MeasurableSpace.prod inferInstance (usualBrownianSigma P 1) ≤
      MeasurableSpace.prod inferInstance
        (inferInstance : MeasurableSpace (NullMeasurableSpace BrownianPath P)) from
      sup_le_sup le_rfl (MeasurableSpace.comap_mono (usualBrownianSigma_le_completion P 1))) le_rfl
  have hf : Measurable (fun p : Time × NullMeasurableSpace BrownianPath P =>
      (⟨p.1, p.1.property.2⟩ : Set.Iic (1 : Time))) := measurable_fst.subtype_mk
  exact h.comp (hf.prodMk measurable_snd)

lemma progressive_time_measurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (ω : BrownianPath) :
    Measurable (fun t : Time => v t ω) :=
  (progressive_joint_complete P hv).comp (measurable_id.prodMk measurable_const)

lemma drift_sq_le_cost (m : Trial) (v : Time → ℝ) (hv : Measurable v)
    (hc : (∫⁻ t, ENNReal.ofReal (m t * v t ^ 2) ∂timeLaw) < ∞) :
    (∫ t, m t * v t ∂timeLaw) ^ 2 ≤
      (∫⁻ t, ENNReal.ofReal (m t * v t ^ 2) ∂timeLaw).toReal := by
  have hm : Integrable m timeLaw :=
    (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simpa [abs_of_nonneg (m.nonneg t)] using m.le_one t)
  have hq : Integrable (fun t => m t * v t ^ 2) timeLaw :=
    ⟨(m.measurable.mul (hv.pow_const 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t =>
        mul_nonneg (m.nonneg t) (sq_nonneg _))).mpr hc⟩
  have hi : Integrable (fun t => m t * v t) timeLaw := by
    apply (hq.add hm).mono' (m.measurable.mul hv).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    change |m t * v t| ≤ m t * v t ^ 2 + m t
    rw [abs_mul, abs_of_nonneg (m.nonneg t)]
    have h := sq_nonneg (|v t| - 1)
    have habs : |v t| ≤ v t ^ 2 + 1 := by nlinarith [sq_abs (v t)]
    calc
      _ ≤ m t * (v t ^ 2 + 1) := mul_le_mul_of_nonneg_left habs (m.nonneg t)
      _ = _ := by ring
  let D := ∫ t, m t * v t ∂timeLaw
  have hnon : 0 ≤ ∫ t, (m t * v t ^ 2 - 2 * D * (m t * v t) + D^2 * m t) ∂timeLaw := by
    apply integral_nonneg
    intro t
    change 0 ≤ m t * v t ^ 2 - 2 * D * (m t * v t) + D^2 * m t
    nlinarith [mul_nonneg (m.nonneg t) (sq_nonneg (v t - D))]
  have hs : Integrable (fun t => m t * v t ^ 2 - 2 * D * (m t * v t)) timeLaw :=
    hq.sub (hi.const_mul (2*D))
  rw [integral_add hs (hm.const_mul (D^2)),
    integral_sub hq (hi.const_mul (2*D)), integral_const_mul, integral_const_mul] at hnon
  have hmone : (∫ t, m t ∂timeLaw) ≤ 1 := by
    calc
      _ ≤ ∫ _ : Time, (1 : ℝ) ∂timeLaw := integral_mono hm (integrable_const _) m.le_one
      _ = _ := by simp
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
    hq.aestronglyMeasurable]
  change D ^ 2 ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hmone (sq_nonneg D)]

def controlDrift (m : Trial) (v : Time → BrownianPath → ℝ) (ω : BrownianPath) : ℝ :=
  ∫ t, m t * v t ω ∂timeLaw

def pathControlCost (m : Trial) (v : Time → BrownianPath → ℝ) (ω : BrownianPath) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (m t * v t ω ^ 2) ∂timeLaw

lemma controlDrift_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (controlDrift m v) P := by
  have h : Measurable (fun ω : NullMeasurableSpace BrownianPath P => controlDrift m v ω) :=
    ((m.measurable.comp measurable_fst).mul
      (progressive_joint_complete P hv)).stronglyMeasurable.integral_prod_left'.measurable
  exact (show NullMeasurable (controlDrift m v) P from h).aemeasurable

lemma pathControlCost_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (pathControlCost m v) P := by
  have h : Measurable (fun ω : NullMeasurableSpace BrownianPath P => pathControlCost m v ω) :=
    ((m.measurable.comp measurable_fst).mul
      ((progressive_joint_complete P hv).pow_const 2)).ennreal_ofReal.lintegral_prod_left'
  exact (show NullMeasurable (pathControlCost m v) P from h).aemeasurable

lemma controlDrift_sq_integrable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hc : controlCost P m v < ∞) :
    Integrable (fun ω => controlDrift m v ω ^ 2) P := by
  have hm := pathControlCost_aemeasurable P m hv
  have hfin : ∀ᵐ ω ∂P, pathControlCost m v ω < ∞ := ae_lt_top' hm hc.ne
  apply (integrable_toReal_of_lintegral_ne_top hm hc.ne).mono'
    ((controlDrift_aemeasurable P m hv).pow_const 2).aestronglyMeasurable
  filter_upwards [hfin] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact drift_sq_le_cost m (fun t => v t ω) (progressive_time_measurable P hv ω) hω

lemma integral_controlDrift_sq_le (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hc : controlCost P m v < ∞) :
    (∫ ω, controlDrift m v ω ^ 2 ∂P) ≤ (controlCost P m v).toReal := by
  have hm := pathControlCost_aemeasurable P m hv
  have hfin : ∀ᵐ ω ∂P, pathControlCost m v ω < ∞ := ae_lt_top' hm hc.ne
  calc
    _ ≤ ∫ ω, (pathControlCost m v ω).toReal ∂P := by
      apply integral_mono_ae (controlDrift_sq_integrable P m hv hc)
        (integrable_toReal_of_lintegral_ne_top hm hc.ne)
      filter_upwards [hfin] with ω hω
      exact drift_sq_le_cost m (fun t => v t ω) (progressive_time_measurable P hv ω) hω
    _ = _ := integral_toReal hm hfin

lemma brownianEval_one_sq_integral (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) : (∫ ω, brownianEval 1 ω ^ 2 ∂P) = 1 := by
  have hm := (hB.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two
  have h := hB.covariance_eval 1 1
  rw [covariance_eq_sub hm hm, hB.integral_eval, zero_mul, sub_zero] at h
  simpa only [sq, min_self, NNReal.coe_one, Pi.mul_apply] using h

lemma controlledTerminal_sq_integral_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hc : controlCost P m v < ∞) :
    (∫ ω, (brownianEval 1 ω + controlDrift m v ω)^2 ∂P) ≤
      2 + 2 * (controlCost P m v).toReal := by
  have hb := (hB.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two
  have hd := (memLp_two_iff_integrable_sq
    (controlDrift_aemeasurable P m hv).aestronglyMeasurable).mpr
    (controlDrift_sq_integrable P m hv hc)
  calc
    _ ≤ ∫ ω, (2 * brownianEval 1 ω ^ 2 + 2 * controlDrift m v ω ^ 2) ∂P := by
      apply integral_mono (hb.add hd).integrable_sq
        ((hb.integrable_sq.const_mul 2).add (hd.integrable_sq.const_mul 2))
      intro ω
      change (brownianEval 1 ω + controlDrift m v ω)^2 ≤
        2 * brownianEval 1 ω ^ 2 + 2 * controlDrift m v ω ^ 2
      nlinarith [sq_nonneg (brownianEval 1 ω - controlDrift m v ω)]
    _ = 2 + 2 * ∫ ω, controlDrift m v ω ^ 2 ∂P := by
      rw [integral_add (hb.integrable_sq.const_mul 2) (hd.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul, brownianEval_one_sq_integral P hB]
      ring
    _ ≤ _ := by linarith [integral_controlDrift_sq_le P m hv hc]

lemma controlledTerminal_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (fun ω => brownianEval 1 ω + controlDrift m v ω) P :=
  (brownianEval_measurable 1).aemeasurable.add (controlDrift_aemeasurable P m hv)

lemma controlReward_integrable (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) {v : Time → BrownianPath → ℝ}
    (hv : Progressive P v) :
    Integrable (fun ω => f (brownianEval 1 ω + controlDrift m v ω)) P := by
  apply (integrable_const ‖f‖).mono'
    (f.continuous.measurable.comp_aemeasurable
      (controlledTerminal_aemeasurable P m hv)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _

end SphericalPerceptron
end
end

end OAI
