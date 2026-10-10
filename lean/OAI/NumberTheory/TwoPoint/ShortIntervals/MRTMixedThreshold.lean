import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAmplificationGrowth

namespace OAI

/-! The factorial and support growth in the amplified cofactor moment
are paid from half of the gap between successive prime thresholds. -/

namespace TwoPointCorrelations

noncomputable def mrtAmplificationCost (r : ℕ) (y a : ℝ) : ℝ :=
  ((r : ℝ) + 1) * Real.log 2 + y +
    2 * (r : ℝ) * Real.log (max 1 (r : ℝ)) + 2 * a * y

lemma mrt_mixed_threshold_exponent {η x y : ℝ} (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 6) (hx : 0 ≤ x) (j r : ℕ)
    (hr : (r : ℝ) * y ≤ x + y)
    (hcost : mrtAmplificationCost r y (mrtFrequencyExponent η j) ≤
      η * x / (2 * ((j : ℝ) + 2) ^ 2)) :
    -2 * mrtFrequencyExponent η (j + 1) * x +
      (((r : ℝ) + 1) * Real.log 2 + y) +
      2 * (r : ℝ) * Real.log (max 1 (r : ℝ)) +
      2 * (r : ℝ) * mrtFrequencyExponent η j * y ≤
      -η * x / (2 * ((j : ℝ) + 2) ^ 2) := by
  have ha := mrtFrequencyExponent_nonneg hη hη' j
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * mrtFrequencyExponent η j
    by positivity)
  have hg := mrt_frequency_gap_saving hη hx j
  have he : 2 * x * (η / (4 * ((j : ℝ) + 2) ^ 2)) =
      η * x / (2 * ((j : ℝ) + 2) ^ 2) := by field_simp; ring
  unfold mrtAmplificationCost at hcost
  nlinarith

theorem mrt_mixed_threshold_bound {η x y τ : ℝ} (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 6) (hx : 0 ≤ x) (hy : 0 ≤ y) (hτ : 0 ≤ τ)
    (j r : ℕ) (hr : (r : ℝ) * y ≤ x + y)
    (hcost : mrtAmplificationCost r y (mrtFrequencyExponent η j) ≤
      η * x / (2 * ((j : ℝ) + 2) ^ 2)) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x) *
        (τ + (2 : ℝ) ^ (r + 1) * Real.exp y) * (r.factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * y) ^ (2 * r) ≤
      (τ + 1) * Real.exp (-η * x / (2 * ((j : ℝ) + 2) ^ 2)) := by
  let g := ((r : ℝ) + 1) * Real.log 2 + y
  let f := 2 * (r : ℝ) * Real.log (max 1 (r : ℝ))
  let d := -(2 * (r : ℝ) * mrtFrequencyExponent η j * y)
  have hpow : (2 : ℝ) ^ (r + 1) * Real.exp y = Real.exp g := by
    rw [mrt_nat_pow_eq_exp (by norm_num), ← Real.exp_add]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    rfl
  have hden : Real.exp (-mrtFrequencyExponent η j * y) ^ (2 * r) =
      Real.exp d := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [d]
    push_cast
    ring
  have hg0 : 0 ≤ g := by
    dsimp [g]
    positivity
  have hg1 : 1 ≤ Real.exp g := Real.one_le_exp_iff.mpr hg0
  have hsum : τ + Real.exp g ≤ (τ + 1) * Real.exp g := by nlinarith
  rw [hpow, hden]
  calc
    _ ≤ Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x) *
        ((τ + 1) * Real.exp g) * Real.exp f / Real.exp d := by
      apply div_le_div_of_nonneg_right _ (Real.exp_pos d).le
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
      · exact mrt_factorial_square_exp r
      · positivity
      · positivity
    _ = (τ + 1) * Real.exp
        (-2 * mrtFrequencyExponent η (j + 1) * x + g + f - d) := by
      have he : Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x + g + f - d) =
          Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x) *
            Real.exp g * Real.exp f / Real.exp d := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_add]
      rw [he]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ τ + 1)
      apply Real.exp_le_exp.mpr
      dsimp [g, f, d]
      convert mrt_mixed_threshold_exponent hη hη' hx j r hr hcost using 1
      ring

lemma mrt_amplification_cost_bound {Y u a : ℝ}
    (hY : 1 ≤ Real.log Y) (hu : 1 ≤ Real.log u) (hY0 : 0 < Y) (hu0 : 0 < u) :
    mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y) a ≤
      (Real.log u / Real.log Y + 2) * Real.log 2 + Real.log Y +
        2 * (Real.log u / Real.log Y + 1) * (Real.log (Real.log u) + 1) +
        2 * a * Real.log Y := by
  have hY1 : 1 < Y := (Real.log_pos_iff hY0.le).mp (by linarith)
  have hu1 : 1 ≤ u := (Real.log_nonneg_iff hu0).mp (by linarith)
  have hr := (mrt_amplification_order_bounds hY1 hu1).2.2.le
  have hc := mrt_amplification_log_cost hY hu hY0 hu0
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_right (add_le_add_right hr 1) hlog2
  unfold mrtAmplificationCost
  nlinarith

theorem mrt_mixed_threshold_amplification {η Y u τ : ℝ} (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 6) (hY : 1 < Y) (hu : 1 ≤ u) (hτ : 0 ≤ τ) (j : ℕ)
    (hcost : mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y)
        (mrtFrequencyExponent η j) ≤
      η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder Y u + 1) * Y) *
        ((mrtAmplificationOrder Y u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder Y u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hy := Real.log_pos hY
  have hr := mul_le_mul_of_nonneg_right
    (mrt_amplification_order_bounds hY hu).2.2.le hy.le
  rw [add_mul, div_mul_cancel₀ _ hy.ne', one_mul] at hr
  simpa only [Real.exp_log (by linarith : 0 < Y)] using
    mrt_mixed_threshold_bound hη hη' (Real.log_nonneg hu) hy.le hτ j
      (mrtAmplificationOrder Y u) hr hcost

end TwoPointCorrelations

end OAI
