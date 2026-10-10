import OAI.Probability.SLE.Gauge.ExactGaugeComparison

namespace OAI

/-! Continuous monotone completions of the explicit and exponent-one log-log gauges. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

namespace GaugeCompletion

def cutoff : ℝ := Real.exp 1

def tailProfile (d q x : ℝ) : ℝ := Real.exp (-d * x) * (Real.log x) ^ q

def completed (d q r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else tailProfile d q (max cutoff (Real.log (1 / r)))

lemma cutoff_one_lt : 1 < cutoff := Real.one_lt_exp_iff.mpr zero_lt_one

lemma cutoff_pos : 0 < cutoff := Real.exp_pos 1

lemma log_one_le {x : ℝ} (hx : cutoff ≤ x) : 1 ≤ Real.log x := by
  simpa only [cutoff, Real.log_exp] using Real.log_le_log cutoff_pos hx

lemma tailProfile_pos {d q x : ℝ} (hx : cutoff ≤ x) : 0 < tailProfile d q x := by
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le (log_one_le hx)) _)

lemma tailProfile_continuousAt {d q x : ℝ} (hx : cutoff ≤ x) :
    ContinuousAt (tailProfile d q) x := by
  have hxp : 0 < x := cutoff_pos.trans_le hx
  have hlp : 0 < Real.log x := zero_lt_one.trans_le (log_one_le hx)
  exact (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul continuousAt_id)).mul
    ((Real.continuousAt_log hxp.ne').rpow_const (Or.inl hlp.ne'))

lemma tailProfile_hasDerivAt {d q x : ℝ} (hx : cutoff ≤ x) :
    HasDerivAt (tailProfile d q)
      (Real.exp (-d * x) * (Real.log x) ^ (q - 1) *
        (q / x - d * Real.log x)) x := by
  have hxp : 0 < x := cutoff_pos.trans_le hx
  have hlp : 0 < Real.log x := zero_lt_one.trans_le (log_one_le hx)
  have he := ((hasDerivAt_id x).const_mul (-d)).exp
  have hl := (Real.hasDerivAt_log hxp.ne').rpow_const (p := q) (Or.inl hlp.ne')
  convert he.mul hl using 1 <;> try rfl
  simp only [id_eq]
  rw [Real.rpow_sub_one hlp.ne']
  field_simp
  ring

lemma tailProfile_antitoneOn {d q : ℝ} (hd : 1 ≤ d) (hq : q ≤ 1) :
    AntitoneOn (tailProfile d q) (Ici cutoff) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (fun x hx => (tailProfile_continuousAt hx).continuousWithinAt)
    (fun x hx => (tailProfile_hasDerivAt (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have hxc : cutoff ≤ x := interior_subset hx
  have hxp : 0 < x := cutoff_pos.trans_le hxc
  have hx1 : 1 ≤ x := cutoff_one_lt.le.trans hxc
  have hl : 1 ≤ Real.log x := log_one_le hxc
  have hdlog : 1 ≤ d * Real.log x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hl)]
  have hdiv : q / x ≤ 1 := (div_le_one hxp).mpr (hq.trans hx1)
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

lemma tailProfile_tendsto_zero {d q : ℝ} (hd : 0 < d) (hq : q ≤ 1) :
    Tendsto (tailProfile d q) atTop (𝓝 0) := by
  have hu : Tendsto (fun x : ℝ => x * Real.exp (-d * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 d hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop cutoff] with x hx
    exact (tailProfile_pos hx).le
  · filter_upwards [eventually_ge_atTop cutoff] with x hx
    have hxp : 0 < x := cutoff_pos.trans_le hx
    have hpow : (Real.log x) ^ q ≤ Real.log x := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (log_one_le hx) hq
    change Real.exp (-d * x) * (Real.log x) ^ q ≤ _
    rw [mul_comm (Real.exp (-d * x))]
    exact mul_le_mul_of_nonneg_right (hpow.trans (Real.log_le_self hxp.le))
      (Real.exp_pos _).le

lemma log_inv_tendsto_atTop :
    Tendsto (fun r : ℝ => Real.log (1 / r)) (𝓝[>] 0) atTop := by
  simpa only [one_div, Function.comp_def] using
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

@[simp] lemma completed_zero (d q : ℝ) : completed d q 0 = 0 := by
  simp [completed]

lemma completed_eq_tail_eventually (d q : ℝ) :
    completed d q =ᶠ[𝓝[>] 0] fun r => tailProfile d q (Real.log (1 / r)) := by
  filter_upwards [self_mem_nhdsWithin,
    log_inv_tendsto_atTop.eventually (eventually_ge_atTop cutoff)] with r hr hx
  have hrp : 0 < r := hr
  simp only [completed, not_le.mpr hrp, ↓reduceIte, max_eq_right hx]

lemma completed_tendsto_zero {d q : ℝ} (hd : 0 < d) (hq : q ≤ 1) :
    Tendsto (completed d q) (𝓝[>] 0) (𝓝 0) := by
  exact ((tailProfile_tendsto_zero hd hq).comp log_inv_tendsto_atTop).congr'
    (completed_eq_tail_eventually d q).symm

lemma completed_continuousAt_pos {d q r : ℝ} (hr : 0 < r) :
    ContinuousAt (completed d q) r := by
  have hc : ContinuousAt
      (fun r : ℝ => tailProfile d q (max cutoff (Real.log (1 / r)))) r := by
    have hg : ContinuousAt (fun r : ℝ => max cutoff (Real.log (1 / r))) r :=
      continuousAt_const.max
      ((continuousAt_const.div continuousAt_id hr.ne').log (one_div_ne_zero hr.ne'))
    exact ContinuousAt.comp (g := tailProfile d q)
      (f := fun r : ℝ => max cutoff (Real.log (1 / r)))
      (tailProfile_continuousAt (show cutoff ≤ max cutoff (Real.log (1 / r))
        from le_max_left _ _)) hg
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with x hx
  have hxp : 0 < x := hx
  simp [completed, not_le.mpr hxp]

lemma completed_monotoneOn {d q : ℝ} (hd : 1 ≤ d) (hq : q ≤ 1) :
    MonotoneOn (completed d q) (Ici 0) := by
  intro r hr s hs hrs
  by_cases hrz : r = 0
  · subst r
    rw [completed_zero]
    by_cases hsz : s = 0
    · subst s
      simp
    · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hsz)
      simp only [completed, not_le.mpr hsp, ↓reduceIte]
      exact (tailProfile_pos (le_max_left _ _)).le
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hrz)
    have hsp : 0 < s := hrp.trans_le hrs
    simp only [completed, not_le.mpr hrp, not_le.mpr hsp, ↓reduceIte]
    apply (tailProfile_antitoneOn hd hq)
      (show cutoff ≤ max cutoff (Real.log (1 / s)) from le_max_left _ _)
      (show cutoff ≤ max cutoff (Real.log (1 / r)) from le_max_left _ _)
    apply max_le_max_left
    exact Real.log_le_log (one_div_pos.mpr hsp)
      (one_div_le_one_div_of_le hrp hrs)

theorem completed_isGauge {d q : ℝ} (hd : 1 ≤ d) (hq : q ≤ 1) :
    IsGauge (completed d q) := by
  refine ⟨?_, completed_monotoneOn hd hq, completed_zero d q, ?_⟩
  · intro r hr
    obtain rfl | hrp := (show 0 ≤ r from hr).eq_or_lt
    · apply continuousWithinAt_Ioi_iff_Ici.mp
      simpa only [ContinuousWithinAt, completed_zero] using
        completed_tendsto_zero (zero_lt_one.trans_le hd) hq
    · exact (completed_continuousAt_pos hrp).continuousWithinAt
  · intro r hr
    simp only [completed, not_le.mpr hr, ↓reduceIte]
    exact tailProfile_pos (le_max_left _ _)

lemma tailProfile_log_inv {d q r : ℝ} (hr : 0 < r) :
    tailProfile d q (Real.log (1 / r)) =
      r ^ d * (Real.log (Real.log (1 / r))) ^ q := by
  unfold tailProfile
  congr 1
  rw [Real.rpow_def_of_pos hr]
  congr 1
  simp only [one_div, Real.log_inv]
  ring

lemma completed_small_formula (d q : ℝ) :
    completed d q =ᶠ[𝓝[>] 0]
      fun r => r ^ d * (Real.log (Real.log (1 / r))) ^ q := by
  filter_upwards [completed_eq_tail_eventually d q, self_mem_nhdsWithin] with r he hr
  exact he.trans (tailProfile_log_inv hr)

end GaugeCompletion

/-- A fixed, deterministic continuous nondecreasing completion of the explicit
exact Hausdorff gauge. -/
def explicitGauge (κ : ℝ) : ℝ → ℝ :=
  GaugeCompletion.completed (dimension κ) (codimension κ / 2)

/-- A deterministic completion of the exponent-one log-log gauge proposed by
Schramm. -/
def schrammGauge (κ : ℝ) : ℝ → ℝ :=
  GaugeCompletion.completed (dimension κ) 1

theorem explicitGauge_isGauge {κ : ℝ} (hκ : 0 < κ) : IsGauge (explicitGauge κ) := by
  apply GaugeCompletion.completed_isGauge
  · dsimp [dimension]
    linarith
  · dsimp [codimension, dimension]
    linarith

theorem explicitGauge_small_formula (κ : ℝ) :
    HasSmallRadiusFormula (explicitGauge κ) (hFormula κ) :=
  GaugeCompletion.completed_small_formula _ _

theorem schrammGauge_isGauge {κ : ℝ} (hκ : 0 < κ) : IsGauge (schrammGauge κ) := by
  apply GaugeCompletion.completed_isGauge
  · dsimp [dimension]
    linarith
  · exact le_rfl

theorem schrammGauge_small_formula (κ : ℝ) :
    HasSmallRadiusFormula (schrammGauge κ) (gFormula κ) := by
  change GaugeCompletion.completed (dimension κ) 1 =ᶠ[𝓝[>] 0]
    fun r => r ^ dimension κ * Real.log (Real.log (1 / r))
  simpa only [Real.rpow_one] using
    GaugeCompletion.completed_small_formula (dimension κ) 1

theorem exists_explicitGauge {κ : ℝ} (hκ : 0 < κ) :
    ∃ h : ℝ → ℝ, IsGauge h ∧ HasSmallRadiusFormula h (hFormula κ) :=
  ⟨explicitGauge κ, explicitGauge_isGauge hκ, explicitGauge_small_formula κ⟩

end SLEExactGauge

end

end OAI
