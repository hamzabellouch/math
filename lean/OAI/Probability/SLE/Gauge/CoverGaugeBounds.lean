import OAI.Probability.SLE.Gauge.GaugeCompletion

namespace OAI

/-!
The uniform gauge cost estimate in the finite-cover step of
`prop:dense-cover-upper`, *An explicit exact Hausdorff gauge for SLE*.
The window starts at `floor (n / 3)`; the intermediate estimate uses
`n / 4` so it also covers that endpoint once `n` is large.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

namespace CoverGaugeBounds

def radius (T : ℝ) (j : ℕ) : ℝ := Real.exp (-T * (j : ℝ))

lemma radius_pos (T : ℝ) (j : ℕ) : 0 < radius T j := Real.exp_pos _

lemma exp_scale_tendsto_zero {T : ℝ} (hT : 0 < T) :
    Tendsto (fun x : ℝ => Real.exp (-T * x)) atTop (𝓝 0) := by
  simpa only [Real.rpow_zero, one_mul] using
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 T hT

lemma radius_tendsto_zero {T : ℝ} (hT : 0 < T) :
    Tendsto (radius T) atTop (𝓝 0) :=
  (exp_scale_tendsto_zero hT).comp tendsto_natCast_atTop_atTop

lemma scaled_quarter_radius_tendsto_zero {C T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => C * Real.exp (-T * ((n : ℝ) / 4))) atTop (𝓝 0) := by
  convert ((exp_scale_tendsto_zero (div_pos hT (by norm_num : (0 : ℝ) < 4))).comp
    tendsto_natCast_atTop_atTop).const_mul C using 1
  · funext n
    dsimp only [Function.comp_def]
    congr 2
    ring
  · simp only [mul_zero]

lemma logLog_scaled_radius {C T j : ℝ} (hC : 0 < C) :
    Real.log (Real.log (1 / (C * Real.exp (-T * j)))) =
      Real.log (T * j - Real.log C) := by
  congr 1
  rw [one_div, Real.log_inv, Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- Once the clock argument is at least `e`, its log-log factor is bounded by
`(2 log n)^q` uniformly for every index below `n`. -/
lemma formula_bound {κ C T n j : ℝ} (hκ8 : κ < 8) (hC : 0 < C)
    (hT : 0 < T) (hn : 1 ≤ n) (hN : T + |Real.log C| ≤ n)
    (hj : j ≤ n) (harg : Real.exp 1 ≤ T * j - Real.log C) :
    hFormula κ (C * Real.exp (-T * j)) ≤
      (C ^ dimension κ * (2 : ℝ) ^ (codimension κ / 2)) *
        Real.exp (-T * j) ^ dimension κ * (Real.log n) ^ (codimension κ / 2) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hq : 0 ≤ codimension κ / 2 := by dsimp [codimension, dimension]; linarith
  have harg0 : 0 < T * j - Real.log C := (Real.exp_pos 1).trans_le harg
  have hlog0 : 0 ≤ Real.log (T * j - Real.log C) := by
    have he : 1 ≤ T * j - Real.log C :=
      (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans harg
    exact Real.log_nonneg he
  have hupper : T * j - Real.log C ≤ n ^ 2 := by
    calc
      _ ≤ T * n + |Real.log C| := by
        have hmul := mul_le_mul_of_nonneg_left hj hT.le
        linarith [neg_le_abs (Real.log C)]
      _ ≤ (T + |Real.log C|) * n := by
        nlinarith [abs_nonneg (Real.log C)]
      _ ≤ n ^ 2 := by
        have hh := mul_le_mul_of_nonneg_right hN hn0.le
        nlinarith
  have hlog : Real.log (T * j - Real.log C) ≤ 2 * Real.log n := by
    have hh := Real.log_le_log harg0 hupper
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  unfold hFormula
  rw [logLog_scaled_radius hC, Real.mul_rpow hC.le (Real.exp_pos _).le]
  calc
    _ ≤ (C ^ dimension κ * Real.exp (-T * j) ^ dimension κ) *
        (2 * Real.log n) ^ (codimension κ / 2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog0 hlog hq) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.log_nonneg hn)]
      ring

/-- The selected disks' diameter costs have one uniform constant across the
whole linear window of clock indices. -/
theorem eventual_window_bound {κ C T : ℝ} (hκ8 : κ < 8) (hC : 0 < C) (hT : 0 < T)
    {h : ℝ → ℝ} (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      (n : ℝ) / 4 ≤ (j : ℝ) → j ≤ n →
      h (C * radius T j) ≤ A * radius T j ^ dimension κ *
        (Real.log (n : ℝ)) ^ (codimension κ / 2) := by
  obtain ⟨δ, hδ, heq⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hf
  refine ⟨C ^ dimension κ * (2 : ℝ) ^ (codimension κ / 2), by positivity, ?_⟩
  have hsmall := (scaled_quarter_radius_tendsto_zero (C := C) hT).eventually (gt_mem_nhds hδ)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      max 1 (max (T + |Real.log C|) (4 * (Real.exp 1 + |Real.log C|) / T)) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hsmall, hlarge] with n hnsmall hnlarge
  intro j hjlow hjhigh
  have hn1 : 1 ≤ (n : ℝ) := (le_max_left _ _).trans hnlarge
  have hN : T + |Real.log C| ≤ (n : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hnlarge)
  have hnclock : 4 * (Real.exp 1 + |Real.log C|) / T ≤ (n : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hnlarge)
  have harg : Real.exp 1 ≤ T * (j : ℝ) - Real.log C := by
    have hb := (div_le_iff₀ hT).mp hnclock
    have hj := mul_le_mul_of_nonneg_left hjlow hT.le
    linarith [le_abs_self (Real.log C)]
  have hrad : C * radius T j < δ := by
    apply lt_of_le_of_lt _ hnsmall
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hjlow (neg_nonpos.mpr hT.le)
  rw [heq ⟨mul_pos hC (radius_pos T j), hrad⟩]
  exact formula_bound hκ8 hC hT hn1 hN (by exact_mod_cast hjhigh) harg

lemma quarter_le_floor_third {n : ℕ} (hn : 12 ≤ n) :
    (n : ℝ) / 4 ≤ (⌊(n : ℝ) / 3⌋₊ : ℝ) := by
  have hf := Nat.lt_floor_add_one ((n : ℝ) / 3)
  have hnreal : (12 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The source uses `J₀ = floor (n/3)`, so the endpoint is included in the
uniform estimate rather than silently replaced by `n/3`. -/
theorem eventual_floor_window_bound {κ C T : ℝ} (hκ8 : κ < 8) (hC : 0 < C) (hT : 0 < T)
    {h : ℝ → ℝ} (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      ⌊(n : ℝ) / 3⌋₊ ≤ j → j ≤ n →
      h (C * radius T j) ≤ A * radius T j ^ dimension κ *
        (Real.log (n : ℝ)) ^ (codimension κ / 2) := by
  obtain ⟨A, hA, hbound⟩ := eventual_window_bound hκ8 hC hT hf
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 12] with n hn hn12
  intro j hj hjn
  exact hn j ((quarter_le_floor_third hn12).trans (by exact_mod_cast hj)) hjn

/-- In particular the largest selected diameter, at the first tested clock
index, tends to zero. -/
theorem floor_window_diameter_tendsto_zero {C T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => C * radius T ⌊(n : ℝ) / 3⌋₊) atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => ⌊(n : ℝ) / 3⌋₊) atTop atTop := by
    apply tendsto_nat_floor_atTop.comp
    exact (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 3))
  simpa only [Function.comp_def, mul_zero] using ((radius_tendsto_zero hT).comp hindex).const_mul C

end CoverGaugeBounds

end SLEExactGauge

end

end OAI
