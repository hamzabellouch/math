import OAI.NumberTheory.TwoPoint.Walks.ColumnCode
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Absorbing the sublinear endpoint and exceptional-position costs. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_sublinear_log_cost (d C : ℝ) (hd : d < 1) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, C * L ^ d * Real.log L ≤ L := by
  by_cases hzero : C = 0
  · filter_upwards [eventually_ge_atTop 0] with L hL
    simpa only [hzero, zero_mul] using hL
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  have hb := (isLittleO_log_rpow_atTop (show 0 < 1 - d by linarith)).bound
    (show 0 < 1 / C by positivity)
  filter_upwards [eventually_ge_atTop 1, hb] with L hL hb
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hb
  calc
    C * L ^ d * Real.log L ≤ C * L ^ d * ((1 / C) * L ^ (1 - d)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (C * (1 / C)) * (L ^ d * L ^ (1 - d)) := by ring
    _ = L := by
      rw [mul_one_div_cancel hzero, one_mul, ← Real.rpow_add hLp,
        show d + (1 - d) = 1 by ring, Real.rpow_one]

lemma eventually_forest_endpoint_cost (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, C * L ^ (0.92 : ℝ) * Real.log (4 * L) ≤ L := by
  filter_upwards [eventually_ge_atTop 4,
    eventually_sublinear_log_cost 0.92 (2 * C) (by norm_num) (by positivity)] with L hL hc
  have hLp : 0 < L := by linarith
  have hlog : Real.log (4 * L) ≤ 2 * Real.log L := by
    rw [Real.log_mul (by norm_num) hLp.ne']
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hL
    linarith
  calc
    _ ≤ C * L ^ (0.92 : ℝ) * (2 * Real.log L) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (2 * C) * L ^ (0.92 : ℝ) * Real.log L := by ring
    _ ≤ L := hc

/-- The exponent constant is absolute. Fixed coefficients in the
sublinear segment budget only change the lower threshold for `L`. -/
theorem eventually_column_code_exponential (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ k N segments omitted imperfect : ℕ,
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 1 ≤ N → N ≤ 4 * k →
      ((2 * segments + omitted + imperfect : ℕ) : ℝ) ≤ C * L ^ (0.92 : ℝ) →
      (Fintype.card (ColumnCode N segments omitted imperfect) : ℝ) ≤
        Real.exp (44 * k) := by
  filter_upwards [eventually_ge_atTop 4, eventually_forest_endpoint_cost C hC] with L hL hcost
  intro k N segments omitted imperfect hklo hkhi hN hNk hM
  let M := 2 * segments + omitted + imperfect
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNreal : (N : ℝ) ≤ 4 * L := by
    have h := (show (N : ℝ) ≤ 4 * k by exact_mod_cast hNk)
    linarith
  have hlogN : Real.log N ≤ Real.log (4 * L) := Real.log_le_log hNpos hNreal
  have hlogpos : 0 ≤ Real.log (4 * L) := Real.log_nonneg (by linarith)
  have hMcost : (M : ℝ) * Real.log N ≤ L := by
    calc
      _ ≤ (M : ℝ) * Real.log (4 * L) := mul_le_mul_of_nonneg_left hlogN (by positivity)
      _ ≤ (C * L ^ (0.92 : ℝ)) * Real.log (4 * L) :=
        mul_le_mul_of_nonneg_right hM hlogpos
      _ ≤ L := hcost
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbits : (2 : ℝ) ^ (5 * N + 1) ≤ Real.exp (5 * N + 1) := by
    calc
      _ ≤ (Real.exp 1) ^ (5 * N + 1) := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hcard : (Fintype.card (ColumnCode N segments omitted imperfect) : ℝ) ≤
      (2 : ℝ) ^ (5 * N + 1) * (N : ℝ) ^ M := by
    exact_mod_cast card_columnCode_le N segments omitted imperfect
  calc
    _ ≤ (2 : ℝ) ^ (5 * N + 1) * (N : ℝ) ^ M := hcard
    _ ≤ Real.exp (5 * N + 1) * Real.exp ((M : ℝ) * Real.log N) := by
      rw [Real.exp_nat_mul, Real.exp_log hNpos]
      exact mul_le_mul_of_nonneg_right hbits (by positivity)
    _ = Real.exp ((5 * N + 1) + (M : ℝ) * Real.log N) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (44 * k) := by
      apply Real.exp_le_exp.mpr
      have hNbound : (N : ℝ) ≤ 4 * k := by exact_mod_cast hNk
      linarith

end TwoPointCorrelations

end OAI
