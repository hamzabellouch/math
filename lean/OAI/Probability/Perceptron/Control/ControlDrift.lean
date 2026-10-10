import Mathlib
import OAI.Probability.Perceptron.Variational.Trial

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma abs_hamiltonian_update_sub_le (α : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α N) (a : Fin (patternCount α N)) (y : Fin N → ℝ) (x : Spin N) :
    |hamiltonian α φ N (Function.update g a y) x - hamiltonian α φ N g x| ≤ 2 * ‖φ‖ := by
  classical
  have heq : hamiltonian α φ N (Function.update g a y) x - hamiltonian α φ N g x =
      φ (patternField (Function.update g a y) a x) - φ (patternField g a x) := by
    unfold hamiltonian
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single a
    · intro b _ hba
      simp [patternField, Function.update_of_ne hba]
    · simp
  rw [heq]
  calc
    _ ≤ |φ (patternField (Function.update g a y) a x)| + |φ (patternField g a x)| :=
      abs_sub _ _
    _ ≤ ‖φ‖ + ‖φ‖ := add_le_add (φ.norm_coe_le_norm _) (φ.norm_coe_le_norm _)
    _ = _ := by ring

lemma abs_pressure_update_sub_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) (a : Fin (patternCount α (N + 1))) (y : Fin (N + 1) → ℝ) :
    |pressure α β φ (N + 1) (Function.update g a y) - pressure α β φ (N + 1) g| ≤
      (2 * |β| * ‖φ‖) / (N + 1 : ℝ) := by
  have hh := abs_log_integral_exp_sub_le (sphereLaw (N + 1))
    (integrable_partition α β φ N (Function.update g a y)) (integrable_partition α β φ N g)
    (partition_pos α β φ N (Function.update g a y)) (partition_pos α β φ N g)
    (c := 2 * |β| * ‖φ‖) (fun x => by
      rw [← mul_sub, abs_mul]
      calc
        _ ≤ |β| * (2 * ‖φ‖) := mul_le_mul_of_nonneg_left
          (abs_hamiltonian_update_sub_le α φ (N + 1) g a y x) (abs_nonneg β)
        _ = _ := by ring)
  unfold pressure
  rw [← sub_div, abs_div, abs_of_nonneg (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity)]
  simpa only [Nat.cast_add, Nat.cast_one] using div_le_div_of_nonneg_right hh
    (show 0 ≤ (N + 1 : ℝ) by positivity)

lemma variance_pressure_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    variance (pressure α β φ (N + 1)) (patternLaw α (N + 1)) ≤
      (patternCount α (N + 1) : ℝ) * ((2 * |β| * ‖φ‖) / (N + 1 : ℝ)) ^ 2 := by
  exact variance_pi_le_of_bounded_differences (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
    (patternCount α (N + 1)) (continuous_pressure α β φ N)
    (abs_pressure_le α β φ N) (abs_pressure_update_sub_le α β φ N)

lemma variance_pressure_le_rate (α β : ℝ) (hα : 0 ≤ α) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    variance (pressure α β φ (N + 1)) (patternLaw α (N + 1)) ≤
      α * (2 * |β| * ‖φ‖) ^ 2 / (N + 1 : ℝ) := by
  have hM : (patternCount α (N + 1) : ℝ) ≤ α * (N + 1 : ℝ) := by
    simpa [patternCount] using Nat.floor_le
      (mul_nonneg hα (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity))
  calc
    _ ≤ (patternCount α (N + 1) : ℝ) * ((2 * |β| * ‖φ‖) / (N + 1 : ℝ)) ^ 2 :=
      variance_pressure_le α β φ N
    _ ≤ (α * (N + 1 : ℝ)) * ((2 * |β| * ‖φ‖) / (N + 1 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hM (sq_nonneg _)
    _ = _ := by
      have hn : (N + 1 : ℝ) ≠ 0 := by positivity
      field_simp

lemma pressure_deviation_le (α β : ℝ) (hα : 0 ≤ α) (φ : ℝ →ᵇ ℝ)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    patternLaw α (N + 1)
      {g | ε < |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|} ≤
    ENNReal.ofReal ((α * (2 * |β| * ‖φ‖) ^ 2 / (N + 1 : ℝ)) / ε ^ 2) := by
  have : IsProbabilityMeasure (patternLaw α (N + 1)) := by
    unfold patternLaw
    infer_instance
  have hp : MemLp (pressure α β φ (N + 1)) 2 (patternLaw α (N + 1)) :=
    MemLp.of_bound (continuous_pressure α β φ N).aestronglyMeasurable _
      (Filter.Eventually.of_forall (abs_pressure_le α β φ N))
  calc
    _ ≤ patternLaw α (N + 1)
        {g | ε ≤ |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|} :=
      by
        apply measure_mono
        intro g hg
        change ε < |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)| at hg
        change ε ≤ |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|
        exact le_of_lt hg
    _ ≤ ENNReal.ofReal (variance (pressure α β φ (N + 1)) (patternLaw α (N + 1)) / ε ^ 2) :=
      meas_ge_le_variance_div_sq hp hε
    _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (variance_pressure_le_rate α β hα φ N) (sq_nonneg _))

theorem pressure_concentrates (α β : ℝ) (hα : 0 ≤ α) (φ : ℝ →ᵇ ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => patternLaw α (N + 1)
      {g | ε < |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|})
      atTop (𝓝 0) := by
  have hr : Tendsto (fun N : ℕ =>
      (α * (2 * |β| * ‖φ‖) ^ 2 / (N + 1 : ℝ)) / ε ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero, zero_mul] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const
        (ε ^ 2)
  have he := ENNReal.tendsto_ofReal hr
  simp only [ENNReal.ofReal_zero] at he
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (fun _ => bot_le) (fun N => pressure_deviation_le α β hα φ N ε hε)

theorem pressure_probability_of_expected_limit (α β : ℝ) (hα : 0 ≤ α)
    (φ : ℝ →ᵇ ℝ) (p : ℝ)
    (hp : Tendsto (fun N : ℕ => expectedPressure α β φ (N+1)) atTop (𝓝 p))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => patternLaw α (N+1)
      {g | ε < |pressure α β φ (N+1) g - p|}) atTop (𝓝 0) := by
  have he : ∀ᶠ N in atTop, |expectedPressure α β φ (N+1) - p| < ε/2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hp (ε/2) (by positivity))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (pressure_concentrates α β hα φ (ε/2) (by positivity))
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · filter_upwards [he] with N hN
    apply measure_mono
    intro g hg
    change ε/2 < |pressure α β φ (N+1) g - expectedPressure α β φ (N+1)|
    change ε < |pressure α β φ (N+1) g - p| at hg
    have hh := abs_sub_le (pressure α β φ (N+1) g) (expectedPressure α β φ (N+1)) p
    linarith

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

lemma controlPayoff_compact_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (f g : ℝ →ᵇ ℝ)
    (K R ε : ℝ) (hK : 0 ≤ K) (hR : 0 < R) (hε : 0 ≤ ε)
    (hf : ‖f‖ ≤ K) (hg : ‖g‖ ≤ K)
    (hnear : ∀ x : ℝ, |x| ≤ R → |f x - g x| ≤ ε)
    (m : Trial) {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hc : controlCost P m v < ∞) :
    |controlPayoff P f m v - controlPayoff P g m v| ≤
      ε + (2 * K / R^2) * (2 + 2 * (controlCost P m v).toReal) := by
  let X := fun ω => brownianEval 1 ω + controlDrift m v ω
  have hfI := controlReward_integrable P f m hv
  have hgI := controlReward_integrable P g m hv
  have hX : Integrable (fun ω => X ω ^ 2) P := by
    have hb := (hB.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two
    have hd := (memLp_two_iff_integrable_sq
      (controlDrift_aemeasurable P m hv).aestronglyMeasurable).mpr
      (controlDrift_sq_integrable P m hv hc)
    exact (hb.add hd).integrable_sq
  have hconst : 0 ≤ 2 * K / R ^ 2 := div_nonneg (by positivity) (sq_nonneg _)
  have hbound (x : ℝ) : |f x - g x| ≤ ε + (2*K/R^2)*x^2 := by
    by_cases hx : |x| ≤ R
    · exact (hnear x hx).trans (le_add_of_nonneg_right (mul_nonneg hconst (sq_nonneg _)))
    · have habs : |f x - g x| ≤ 2*K := by
        calc
          _ ≤ |f x| + |g x| := abs_sub _ _
          _ ≤ K + K := add_le_add ((f.norm_coe_le_norm x).trans hf)
            ((g.norm_coe_le_norm x).trans hg)
          _ = _ := by ring
      have hsq : R^2 ≤ x^2 := by nlinarith [sq_abs x, lt_of_not_ge hx]
      have hr : R^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hR)
      have heq : (2*K/R^2)*R^2 = 2*K := div_mul_cancel₀ _ hr
      have hb := mul_le_mul_of_nonneg_left hsq hconst
      rw [heq] at hb
      exact habs.trans (hb.trans (le_add_of_nonneg_left hε))
  have heq : controlPayoff P f m v - controlPayoff P g m v =
      ∫ ω, (f (X ω) - g (X ω)) ∂P := by
    rw [integral_sub hfI hgI]
    unfold controlPayoff controlDrift
    ring
  rw [heq]
  calc
    _ ≤ ∫ ω, |f (X ω) - g (X ω)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (ε + (2*K/R^2)*X ω^2) ∂P :=
      integral_mono (hfI.sub hgI).abs ((integrable_const ε).add (hX.const_mul _))
        (fun ω => hbound (X ω))
    _ = ε + (2*K/R^2) * ∫ ω, X ω^2 ∂P := by
      rw [integral_add (integrable_const ε) (hX.const_mul _), integral_const_mul]
      simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (controlledTerminal_sq_integral_le P hB m hv hc) hconst)

lemma controlValue_le_of_cost_cutoff (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (K b : ℝ) (hf : ‖f‖ ≤ K)
    (hb : -K ≤ b)
    (hsmall : ∀ v : Time → BrownianPath → ℝ, Progressive P v →
      controlCost P m v < ∞ → (controlCost P m v).toReal ≤ 4*K+2 →
      controlPayoff P f m v ≤ b) : controlValue P f m ≤ b := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, hv, hc, rfl⟩
  by_cases hcost : (controlCost P m v).toReal ≤ 4*K+2
  · exact hsmall v hv hc hcost
  · have hr := (abs_le.mp (abs_integral_reward_le P f
      (fun ω => brownianEval 1 ω + ∫ t, m t * v t ω ∂timeLaw))).2
    unfold controlPayoff
    linarith [lt_of_not_ge hcost]

lemma controlValue_compact_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (f g : ℝ →ᵇ ℝ)
    (K R ε : ℝ) (hK : 0 ≤ K) (hR : 0 < R) (hε : 0 ≤ ε)
    (hf : ‖f‖ ≤ K) (hg : ‖g‖ ≤ K)
    (hnear : ∀ x : ℝ, |x| ≤ R → |f x - g x| ≤ ε)
    (m : Trial) :
    |controlValue P f m - controlValue P g m| ≤
      ε + (2 * K / R^2) * (2 + 2 * (4*K+2)) := by
  let δ := ε + (2*K/R^2)*(2+2*(4*K+2))
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hfg : controlValue P f m ≤ controlValue P g m + δ := by
    apply controlValue_le_of_cost_cutoff P f m K _ hf
    · linarith [neg_norm_le_controlValue P g m]
    · intro v hv hc hcost
      have hd := (abs_le.mp (controlPayoff_compact_bound P hB f g K R ε hK hR hε
        hf hg hnear m hv hc)).2
      have hp : controlPayoff P g m v ≤ controlValue P g m :=
        le_csSup (controlPayoffs_bddAbove P g m) ⟨v, hv, hc, rfl⟩
      have hh : ε + (2*K/R^2)*(2+2*(controlCost P m v).toReal) ≤ δ := by
        dsimp [δ]
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      linarith
  have hgf : controlValue P g m ≤ controlValue P f m + δ := by
    apply controlValue_le_of_cost_cutoff P g m K _ hg
    · linarith [neg_norm_le_controlValue P f m]
    · intro v hv hc hcost
      have hd := (abs_le.mp (controlPayoff_compact_bound P hB f g K R ε hK hR hε
        hf hg hnear m hv hc)).1
      have hp : controlPayoff P f m v ≤ controlValue P f m :=
        le_csSup (controlPayoffs_bddAbove P f m) ⟨v, hv, hc, rfl⟩
      have hh : ε + (2*K/R^2)*(2+2*(controlCost P m v).toReal) ≤ δ := by
        dsimp [δ]
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma controlValue_uniform_of_compact (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (f : ℝ →ᵇ ℝ) (fseq : ℕ → ℝ →ᵇ ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hf : ‖f‖ ≤ K) (hseq : ∀ n, ‖fseq n‖ ≤ K)
    (hcomp : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ, |x| ≤ R → |fseq n x - f x| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m : Trial,
      |controlValue P (fseq n) m - controlValue P f m| < ε := by
  intro ε hε
  let C := 2*K*(2+2*(4*K+2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let Q := C / (ε/2)
  have hQ : 0 ≤ Q := div_nonneg hC (by positivity)
  let R := Q+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hQR : Q < R^2 := by dsimp [R]; nlinarith [sq_nonneg Q]
  have hCQ : C = (ε/2)*Q := by dsimp [Q]; field_simp
  have htail : C/R^2 < ε/2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hR)).mpr
    rw [hCQ]
    exact mul_lt_mul_of_pos_left hQR (by positivity)
  obtain ⟨N,hN⟩ := hcomp R hR (ε/2) (by positivity)
  refine ⟨N, fun n hn m => ?_⟩
  have hb := controlValue_compact_bound P hB (fseq n) f K R (ε/2) hK hR
    (by positivity) (hseq n) hf (hN n hn) m
  have heq : (2*K/R^2)*(2+2*(4*K+2)) = C/R^2 := by dsimp [C]; ring
  rw [heq] at hb
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
