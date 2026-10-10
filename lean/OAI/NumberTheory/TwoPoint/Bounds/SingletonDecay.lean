import OAI.NumberTheory.TwoPoint.Walks.RankDecay

namespace OAI

/-! The selected singleton savings dominate the complete crude trace cost. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_singleton_floor_bounds :
    ∀ᶠ L : ℝ in atTop,
      L ^ (1 / 12 : ℝ) / 32 ≤ ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) ∧
        ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) ≤ L := by
  have hr := (tendsto_rpow_atTop (show 0 < (1 / 12 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 32)
  filter_upwards [eventually_ge_atTop 1, hr] with L hL hpow
  have hf := Nat.lt_floor_add_one (L ^ (1 / 12 : ℝ))
  have hd : ⌊L ^ (1 / 12 : ℝ)⌋₊ < 8 * (⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 + 1) := by
    have he := Nat.mod_add_div ⌊L ^ (1 / 12 : ℝ)⌋₊ 8
    have hm := Nat.mod_lt ⌊L ^ (1 / 12 : ℝ)⌋₊ (show 0 < 8 by decide)
    omega
  have hd' : (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) <
      8 * ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) + 8 := by exact_mod_cast hd
  constructor
  · linarith
  · apply (show ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) ≤
        (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) by exact_mod_cast Nat.div_le_self _ 8).trans
    apply (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hL (show (1 / 12 : ℝ) ≤ 1 by norm_num)

/-- `647/600 = 1/12 + 199/200` exceeds the desired exponent `21/20`.
All fixed coefficients in the enumeration affect only the threshold. -/
theorem eventually_singleton_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ r : ℕ,
      L ^ (1 / 12 : ℝ) / 32 ≤ (r : ℝ) → (r : ℝ) ≤ L →
      Real.exp (C * L * (Real.log L) ^ 2) *
        (Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r ≤
          Real.exp (-L ^ (21 / 20 : ℝ)) := by
  have h8 := (tendsto_rpow_atTop (show 0 < (19 / 300 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 8)
  have h64 := (tendsto_rpow_atTop (show 0 < (17 / 600 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 64)
  filter_upwards [eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_crude_cost_small (2 * C) (by positivity), h8, h64] with L hL hlog hcost h8 h64
  intro r hrlo hrhi
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have heq1 : L ^ (203 / 200 : ℝ) * L ^ (19 / 300 : ℝ) = L ^ (647 / 600 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  have heq2 : L ^ (21 / 20 : ℝ) * L ^ (17 / 600 : ℝ) = L ^ (647 / 600 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  have heq3 : L ^ (1 / 12 : ℝ) * L ^ (199 / 200 : ℝ) = L ^ (647 / 600 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hp1 := mul_le_mul_of_nonneg_left h8 (Real.rpow_nonneg hLp.le (203 / 200 : ℝ))
  rw [heq1] at hp1
  have hp2 := mul_le_mul_of_nonneg_left h64 (Real.rpow_nonneg hLp.le (21 / 20 : ℝ))
  rw [heq2] at hp2
  have hnegative := mul_le_mul_of_nonneg_right hrlo
    (Real.rpow_nonneg hLp.le (199 / 200 : ℝ))
  rw [div_mul_eq_mul_div, heq3] at hnegative
  have hpositive := mul_le_mul_of_nonneg_left hrhi
    (show 0 ≤ C * Real.log L by positivity)
  have hlog' : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
  have hpos2 := mul_le_mul_of_nonneg_left hlog' (show 0 ≤ C * L by positivity)
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The one-coordinate progression factor in exponential form. -/
lemma progression_factor_le_exp (N : ℕ) (H T D : ℝ)
    (hH : Real.exp T ≤ H) (hN : 2 + Real.log N ≤ Real.exp D) :
    H⁻¹ + (1 + Real.log N) / H ≤ Real.exp (D - T) := by
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  calc
    _ = (2 + Real.log N) * H⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ Real.exp D * Real.exp (-T) := by
      apply mul_le_mul hN _ (inv_nonneg.mpr hHp.le) (by positivity)
      rw [Real.exp_neg]
      exact inv_anti₀ (Real.exp_pos _) hH
    _ = _ := by simp only [sub_eq_add_neg, Real.exp_add]

/-- The actual cutoffs `N ≤ exp L` and `H ≥ exp(L^(199/200))`
give a progression factor at most one for all sufficiently large `L`. -/
lemma eventually_singleton_progression_factor :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (H : ℝ), 1 ≤ N → (N : ℝ) ≤ Real.exp L →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      H⁻¹ + (1 + Real.log N) / H ≤ Real.exp (2 * Real.log L - L ^ (199 / 200 : ℝ)) ∧
        H⁻¹ + (1 + Real.log N) / H ≤ 1 := by
  have hs := (isLittleO_log_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num)).bound
    (show 0 < (1 / 2 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop 2, hs] with L hL hs
  intro N H hN hNL hH
  have hLp : 0 < L := by linarith
  have hl : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg hl, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hs
  have hlogN : Real.log (N : ℝ) ≤ L := by
    have ht := Real.log_le_log (show (0 : ℝ) < N by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN) hNL
    simpa only [Real.log_exp] using ht
  have hnum : 2 + Real.log N ≤ Real.exp (2 * Real.log L) := by
    have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
      rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
        Real.exp_add, Real.exp_log hLp]
      ring
    rw [he]
    nlinarith
  have hb := progression_factor_le_exp N H (L ^ (199 / 200 : ℝ)) (2 * Real.log L) hH hnum
  refine ⟨hb, hb.trans ?_⟩
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  linarith

/-- Transfer the finite progression estimate to the same exponential
scale. Its harmless numerator `2 + log N` is kept explicitly. -/
theorem eventually_singleton_total (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (r N : ℕ) (H cost total : ℝ),
      L ^ (1 / 12 : ℝ) / 32 ≤ (r : ℝ) → (r : ℝ) ≤ L →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      2 + Real.log N ≤ Real.exp (C * Real.log L) →
      0 ≤ cost → cost ≤ Real.exp (C * L * (Real.log L) ^ 2) →
      total ≤ cost * (H⁻¹ + (1 + Real.log N) / H) ^ r →
      total ≤ Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_singleton_decay C hC] with L hL
  intro r N H cost total hrlo hrhi hH hN hcost hcost' htotal
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hnum : 0 ≤ 2 + Real.log N := by
    by_cases hzero : N = 0
    · simp [hzero]
    · have hn : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
      have hl := Real.log_nonneg hn
      linarith
  have hbase := progression_factor_le_exp N H (L ^ (199 / 200 : ℝ))
    (C * Real.log L) hH hN
  have hnonneg : 0 ≤ H⁻¹ + (1 + Real.log N) / H := by
    rw [show H⁻¹ + (1 + Real.log N) / H = (2 + Real.log N) * H⁻¹ by
      rw [div_eq_mul_inv]; ring]
    positivity
  apply htotal.trans
  calc
    _ ≤ cost * (Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hbase r) hcost
    _ ≤ Real.exp (C * L * (Real.log L) ^ 2) *
        (Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r :=
      mul_le_mul_of_nonneg_right hcost' (by positivity)
    _ ≤ _ := hL r hrlo hrhi

end TwoPointCorrelations

end OAI
