import OAI.Analysis.Mahler.ErrorBound

namespace OAI

namespace SymmetricMahler
open Real MeasureTheory Set

noncomputable def radialCutoff (m : ℝ) : ℝ := 1-log m/m

lemma radial_cutoff_bounds {m : ℝ} (hm : 1 < m) :
    0 ≤ radialCutoff m ∧ radialCutoff m < 1 := by
  have hm0 : 0 < m := by linarith
  have hl := log_le_sub_one_of_pos hm0
  have hp : 0 < log m/m := div_pos (log_pos hm) hm0
  have hlt : log m/m < 1 := (div_lt_one hm0).2 (by linarith)
  dsimp [radialCutoff]
  constructor <;> linarith

/-- A uniform majorant for the unscaled E_m, independent of r₀. -/
noncomputable def errorEnvelope (m : ℝ) : ℝ :=
  2*m*(radialCutoff m)^(2*m-3/2 : ℝ)/sqrt (4/Real.pi^2) +
    sqrt (2/((2/Real.pi^2)*log m))*(1+4/exp 1)

/-- The whole singular error integral is bounded uniformly in its basepoint.
The only analytic premise about M is the radial derivative formula plus
continuity/measurability; every integral estimate and endpoint argument is proved. -/
theorem uniform_error_bound {M : ℝ → ℝ}
    (hM : Measurable M) (hcont : ContinuousOn M (Ico 0 1))
    (hderiv : ∀ r ∈ Ioo 0 1, HasDerivAt M (radialDerivative r) r)
    {m r₀ : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hr₀1 : r₀ < 1) :
    IntervalIntegrable (errorIntegrand M r₀ m) volume r₀ 1 ∧
      (∫ r in r₀..(1 : ℝ), errorIntegrand M r₀ m r) ≤ errorEnvelope m := by
  have hm1 : 1 < m := by linarith
  have hc0 : (0 : ℝ) < 4/Real.pi^2 := by positivity
  have hc1 : 0 < (2/Real.pi^2)*log m := mul_pos (by positivity) (log_pos hm1)
  have hcut := radial_cutoff_bounds hm1
  have hglobal : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < 1 →
      (4/Real.pi^2)*(b-a) ≤ M b-M a := by
    intro a b ha hab hb
    apply radial_increment_lower ha hab hb
    · apply hcont.mono
      intro x hx
      exact ⟨le_trans ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    · intro x hx
      exact hderiv x ⟨lt_of_le_of_lt ha hx.1, lt_trans hx.2 hb⟩
  have hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < 1 → M a ≤ M b := by
    intro a b ha hab hb
    have h := hglobal a b ha hab hb
    have hnonneg := mul_nonneg hc0.le (sub_nonneg.mpr hab)
    linarith
  have hboundary : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < 1 → radialCutoff m ≤ a →
      ((2/Real.pi^2)*log m)*(b-a) ≤ M b-M a := by
    intro a b ha hab hb hlayer
    apply boundary_layer_increment_lower hm1 ha hab hb hlayer
    · apply hcont.mono
      intro x hx
      exact ⟨le_trans ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    · intro x hx
      exact hderiv x ⟨lt_of_le_of_lt ha hx.1, lt_trans hx.2 hb⟩
  have htail : ∀ b : ℝ, r₀ ≤ b → 0 ≤ b → b < 1 → radialCutoff m ≤ b →
      IntervalIntegrable (errorIntegrand M r₀ m) volume b 1 ∧
      (∫ r in b..(1 : ℝ), errorIntegrand M r₀ m r) ≤
        sqrt (2/((2/Real.pi^2)*log m))*(1+4/exp 1) := by
    intro b hr₀b hb hb1 hcb
    have hi : ∀ r ∈ Ioo b 1, ((2/Real.pi^2)*log m)*(r-b) ≤ M r-M r₀ := by
      intro r hr
      have h := hboundary b r hb hr.1.le hr.2 hcb
      have hmb := hmono r₀ b hr₀ hr₀b hb1
      linarith
    exact ⟨outer_error_integrable hM hm hc1 hb hb1 hi,
      outer_error_integral_bound hM hm hc1 hb hb1 hi⟩
  by_cases hsplit : r₀ ≤ radialCutoff m
  · have hi : ∀ r ∈ Ioc r₀ (radialCutoff m), (4/Real.pi^2)*(r-r₀) ≤ M r-M r₀ := by
      intro r hr
      exact hglobal r₀ r hr₀ hr.1.le (lt_of_le_of_lt hr.2 hcut.2)
    have hinner := inner_error_integrable hM hm hc0 hr₀ hsplit hcut.2.le hi
    have hinnerbound := inner_error_integral_bound hM hm hc0 hr₀ hsplit hcut.2.le hi
    have houter := htail (radialCutoff m) hsplit hcut.1 hcut.2 le_rfl
    constructor
    · exact hinner.trans houter.1
    · rw [← intervalIntegral.integral_add_adjacent_intervals hinner houter.1]
      exact add_le_add hinnerbound houter.2
  · have houter := htail r₀ le_rfl hr₀ hr₀1 (le_of_not_ge hsplit)
    refine ⟨houter.1, ?_⟩
    have hinnernonneg : 0 ≤ 2*m*(radialCutoff m)^(2*m-3/2 : ℝ)/sqrt (4/Real.pi^2) := by
      have := hcut.1
      have hm0 : 0 ≤ m := by linarith
      positivity
    exact le_trans houter.2 (by dsimp [errorEnvelope]; linarith)

end SymmetricMahler

namespace SymmetricMahler
open Real Filter
open scoped Topology

/-- A decaying bound for the inner term, weaker than O(m⁻¹)
but sufficient for uniform convergence. -/
theorem cutoff_power_bound {m : ℝ} (hm : 3 ≤ m) :
    m*(radialCutoff m)^(2*m-3/2 : ℝ) ≤ 1/sqrt m := by
  have hmpos : 0 < m := by linarith
  have hm1 : 1 < m := by linarith
  have hcut := radial_cutoff_bounds hm1
  have hlogm := log_le_sub_one_of_pos hmpos
  have hcutpos : 0 < radialCutoff m := by
    dsimp [radialCutoff]
    have hlt : log m/m < 1 := (div_lt_one hmpos).2 (by linarith)
    linarith
  have hpow : (radialCutoff m)^(2*m-3/2 : ℝ) ≤
      exp (-(3*m/2)*(1-radialCutoff m)) := by
    rw [rpow_def_of_pos hcutpos]
    apply exp_le_exp.mpr
    have hlog := log_le_sub_one_of_pos hcutpos
    have hsign := log_nonpos hcut.1 hcut.2.le
    have hneg := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (2*m-3/2)-(3*m/2) by linarith) hsign
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 3*m/2 by linarith)
    nlinarith
  calc
    m*(radialCutoff m)^(2*m-3/2 : ℝ) ≤
        m*exp (-(3*m/2)*(1-radialCutoff m)) :=
      mul_le_mul_of_nonneg_left hpow hmpos.le
    _ = m*m^(-(3/2 : ℝ)) := by
      rw [rpow_def_of_pos hmpos]
      congr 1
      congr 1
      dsimp [radialCutoff]
      field_simp
      ring
    _ = m^(-(1/2 : ℝ)) := by
      conv_lhs => lhs; rw [← rpow_one m]
      rw [← rpow_add hmpos]
      norm_num
    _ = 1/sqrt m := (inverse_sqrt_eq_rpow hmpos.le).symm

/-- The uniform majorant tends to zero; its rate is enough for the planar lemma. -/
theorem error_envelope_tendsto_zero : Tendsto errorEnvelope atTop (𝓝 0) := by
  have hinvsqrt : Tendsto (fun m : ℝ => 1/sqrt m) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop
  have hinnerlim : Tendsto (fun m : ℝ =>
      (2/sqrt (4/Real.pi^2))*(1/sqrt m)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hinvsqrt
  have hinner : Tendsto (fun m : ℝ =>
      2*m*(radialCutoff m)^(2*m-3/2 : ℝ)/sqrt (4/Real.pi^2)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hinnerlim
    · filter_upwards [eventually_ge_atTop (3 : ℝ)] with m hm
      have hm1 : 1 < m := by linarith
      have hc := (radial_cutoff_bounds hm1).1
      have hm0 : 0 ≤ m := by linarith
      positivity
    · filter_upwards [eventually_ge_atTop (3 : ℝ)] with m hm
      have h := mul_le_mul_of_nonneg_left (cutoff_power_bound hm)
        (show 0 ≤ 2/sqrt (4/Real.pi^2) by positivity)
      calc
        _ = (2/sqrt (4/Real.pi^2))*(m*(radialCutoff m)^(2*m-3/2 : ℝ)) := by ring
        _ ≤ _ := h
  have hinvlog : Tendsto (fun m : ℝ => 1/log m) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp tendsto_log_atTop
  have hbase : Tendsto (fun m : ℝ => 2/((2/Real.pi^2)*log m)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => 2/(2/Real.pi^2)) atTop
      (𝓝 (2/(2/Real.pi^2)))).mul hinvlog
    convert h using 1 <;> simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  have hsqrt := continuous_sqrt.continuousAt.tendsto.comp hbase
  have houter : Tendsto (fun m : ℝ =>
      sqrt (2/((2/Real.pi^2)*log m))*(1+4/exp 1)) atTop (𝓝 0) := by
    simpa using hsqrt.mul_const (1+4/exp 1)
  change Tendsto (fun m : ℝ => 2*m*(radialCutoff m)^(2*m-3/2 : ℝ)/sqrt (4/Real.pi^2) +
    sqrt (2/((2/Real.pi^2)*log m))*(1+4/exp 1)) atTop (𝓝 0)
  simpa only [add_zero] using hinner.add houter

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set Filter
open scoped Topology

/-- The exact basepoint-uniform convergence needed in the planar lemma.
No fixed basepoint is chosen before the threshold m₀. -/
theorem uniform_error_small {M : ℝ → ℝ}
    (hM : Measurable M) (hcont : ContinuousOn M (Ico 0 1))
    (hderiv : ∀ r ∈ Ioo 0 1, HasDerivAt M (radialDerivative r) r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → ∀ r₀ ∈ Ico (0 : ℝ) 1,
      IntervalIntegrable (errorIntegrand M r₀ m) volume r₀ 1 ∧
      (∫ r in r₀..(1 : ℝ), errorIntegrand M r₀ m r) < ε := by
  have he : ∀ᶠ m : ℝ in atTop, errorEnvelope m < ε :=
    error_envelope_tendsto_zero.eventually (gt_mem_nhds hε)
  have hboth : ∀ᶠ m : ℝ in atTop, 2 ≤ m ∧ errorEnvelope m < ε :=
    (eventually_ge_atTop (2 : ℝ)).and he
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 hboth
  refine ⟨m₀, ?_⟩
  intro m hmm r₀ hr₀
  have hm := hm₀ m hmm
  have h := uniform_error_bound hM hcont hderiv hm.1 hr₀.1 hr₀.2
  exact ⟨h.1, lt_of_le_of_lt h.2 hm.2⟩

end SymmetricMahler

end OAI
