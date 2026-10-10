import OAI.NumberTheory.TwoPoint.Halasz.HalaszParameters

namespace OAI

/-! A logarithmic cutoff for the general multiplicative correction. -/

namespace TwoPointCorrelations

open Filter

lemma halasz_eventually_correction_scale (X₀ : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let W := ⌈Real.log x ^ 4⌉₊
      2 ≤ W ∧ X₀ ≤ (W : ℝ) ∧ (W : ℝ) ^ 2 ≤ x ∧
      (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / Real.log x ∧
      2 ≤ Real.log x ∧ 1 ≤ Real.log (Real.log x) := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 8)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 2 X₀))
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall, hlog, hll] with x hx hs hl hll
  let ℓ := Real.log x
  let W := ⌈ℓ ^ 4⌉₊
  have hℓ2 : 2 ≤ ℓ := (le_max_left _ _).trans hl
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hp : 1 ≤ ℓ ^ 4 := one_le_pow₀ hℓ1
  have hlow : ℓ ^ 4 ≤ (W : ℝ) := Nat.le_ceil _
  have hhigh : (W : ℝ) ≤ 2 * ℓ ^ 4 := by
    have hh : (W : ℝ) < ℓ ^ 4 + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hℓle : ℓ ≤ ℓ ^ 4 := le_self_pow₀ hℓ1 (by norm_num : (4 : ℕ) ≠ 0)
  have hW2 : 2 ≤ W := by exact_mod_cast hℓ2.trans (hℓle.trans hlow)
  have hWX : X₀ ≤ (W : ℝ) := ((le_max_right _ _).trans hl).trans (hℓle.trans hlow)
  dsimp only [id] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hℓ0.le 8),
    Real.norm_eq_abs, abs_of_pos hx] at hs
  have hWs : (W : ℝ) ^ 2 ≤ x := by
    calc
      _ ≤ (2 * ℓ ^ 4) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg W) hhigh 2
      _ = 4 * ℓ ^ 8 := by ring
      _ ≤ x := by linarith
  have htail : (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / ℓ := by
    calc
      _ ≤ (ℓ ^ 4) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (pow_pos hℓ0 4) hlow (by norm_num)
      _ = 1 / ℓ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le]
        norm_num
        rw [Real.rpow_neg_one]
  exact ⟨hW2, hWX, hWs, htail, hℓ2, hll⟩

lemma halasz_correction_quotient {N W d : ℕ} (hW : 2 ≤ W) (hd : 0 < d)
    (hdW : d ≤ W) (hWN : W ^ 2 ≤ N) :
    W ≤ N / d ∧ N / d ≤ N ∧ N ≤ (N / d) ^ 3 := by
  have hWpos : 0 < W := by omega
  have hWd : W * d ≤ N := (Nat.mul_le_mul_left W hdW).trans (by simpa [pow_two] using hWN)
  have hWq : W ≤ N / d := (Nat.le_div_iff_mul_le hd).mpr hWd
  have hq : 2 ≤ N / d := hW.trans hWq
  have hdq : d ≤ N / d := hdW.trans hWq
  have hn := Nat.lt_mul_div_succ N hd
  refine ⟨hWq, Nat.div_le_self N d, ?_⟩
  have htwo : N / d + 1 ≤ (N / d) ^ 2 := by nlinarith
  calc
    N ≤ d * (N / d + 1) := hn.le
    _ ≤ (N / d) * ((N / d) ^ 2) := Nat.mul_le_mul hdq htwo
    _ = (N / d) ^ 3 := by ring

end TwoPointCorrelations

end OAI
