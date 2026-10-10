import OAI.Probability.SLE.Gauge.DenseCoverCore

namespace OAI

/-! The failure and residual-cover estimates used by the explicit gauge. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- The dimensions in the hit probability, covering cost, and grid count cancel. -/
lemma dense_cover_power_cancellation (κ : ℝ) {r : ℝ} (hr : 0 < r) :
    r ^ (-2 : ℝ) * r ^ dimension κ * r ^ codimension κ = 1 := by
  rw [← Real.rpow_add hr, ← Real.rpow_add hr]
  have he : (-2 : ℝ) + dimension κ + codimension κ = 0 := by
    unfold codimension
    ring
  rw [he, Real.rpow_zero]

lemma failure_product_le_exp {p : ℝ} (hp : p ≤ 1) (N : ℕ) :
    (1 - p) ^ N ≤ Real.exp (-p * (N : ℝ)) := by
  have hb : 1 - p ≤ Real.exp (-p) := by
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-p)
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hp) hb N
  simpa only [← Real.exp_nat_mul, mul_comm (N : ℝ) (-p)] using hpow

/-- A linear number of tests, each succeeding with probability at least
`n^(-1/2)`, has the stretched-exponential failure bound used in the paper. -/
theorem failure_window_le_stretchedExp {n : ℝ} (hn : 1 ≤ n)
    (N : ℕ) (hN : n / 4 ≤ (N : ℝ)) :
    (1 - 1 / Real.sqrt n) ^ N ≤ Real.exp (-Real.sqrt n / 4) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs1 : 1 ≤ Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn
  have hp : 1 / Real.sqrt n ≤ 1 := (div_le_one hs).mpr hs1
  apply (failure_product_le_exp hp N).trans
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hN (one_div_pos.mpr hs).le
  have he : (1 / Real.sqrt n) * (n / 4) = Real.sqrt n / 4 := by
    field_simp
    nlinarith [Real.sq_sqrt hn0.le]
  rw [he] at hmul
  nlinarith

/-- A logarithmic correction cannot offset the stretched-exponential failure
probability obtained from the finite sequence of adapted tests. -/
theorem logarithmic_cleanup_tendsto_zero {q c : ℝ}
    (hq : q ≤ 1) (hc : 0 < c) :
    Tendsto (fun x : ℝ => (Real.log x) ^ q * Real.exp (-c * Real.sqrt x))
      atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc).comp
    Real.tendsto_sqrt_atTop
  have hu : Tendsto (fun x : ℝ => x * Real.exp (-c * Real.sqrt x))
      atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_def, Real.rpow_two, Real.sq_sqrt hx]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have h1 : 1 ≤ x := (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hx
    exact mul_nonneg (Real.rpow_nonneg (Real.log_nonneg h1) q) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hxp : 0 < x := (Real.exp_pos 1).trans_le hx
    have hlog : 1 ≤ Real.log x := by
      simpa using Real.log_le_log (Real.exp_pos 1) hx
    have hp : (Real.log x) ^ q ≤ Real.log x := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog hq
    exact mul_le_mul_of_nonneg_right (hp.trans (Real.log_le_self hxp.le))
      (Real.exp_pos _).le

theorem explicit_cleanup_tendsto_zero {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ (codimension κ / 2) *
      Real.exp (-c * Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
  have hq : codimension κ / 2 ≤ 1 := by
    dsimp [codimension, dimension]
    linarith
  exact (logarithmic_cleanup_tendsto_zero hq hc).comp tendsto_natCast_atTop_atTop

/-- Finite expected residual cost is the sum of each missed-cell probability
times its deterministic covering cost. -/
theorem expected_missed_cell_cost
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (I : Finset ι) (missed : ι → Set Ω)
    (hm : ∀ i ∈ I, MeasurableSet (missed i))
    (cost bound : ι → ℝ≥0∞)
    (hb : ∀ i ∈ I, P (missed i) ≤ bound i) :
    (∫⁻ ω, ∑ i ∈ I, (missed i).indicator (fun _ => cost i) ω ∂P) ≤
      ∑ i ∈ I, cost i * bound i := by
  rw [lintegral_finsetSum I (fun i hi => measurable_const.indicator (hm i hi))]
  apply Finset.sum_le_sum
  intro i hi
  rw [lintegral_indicator (hm i hi), lintegral_const, Measure.restrict_apply_univ]
  exact mul_le_mul' le_rfl (hb i hi)

end SLEExactGauge

end

end OAI
