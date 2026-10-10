import OAI.NumberTheory.TwoPoint.Walks.ForestCodeAsymptotics
import OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder

namespace OAI

/-! Exponential bound for the universal full-column decoder. -/

namespace TwoPointCorrelations

open Filter

/-- The exponent constant is absolute. Fixed coefficients in the
sublinear segment budget only change the lower threshold for `L`. -/
theorem eventually_column_decoder_exponential (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ k N segments omitted imperfect : ℕ,
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 1 ≤ N → N ≤ 4 * k →
      ((2 * segments + omitted + imperfect : ℕ) : ℝ) ≤ C * L ^ (0.92 : ℝ) →
      (Fintype.card (ColumnDecoderCode N segments omitted imperfect) : ℝ) ≤
        Real.exp (52 * k) := by
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
  have hbits : (2 : ℝ) ^ (6 * N + 1) ≤ Real.exp (6 * N + 1) := by
    calc
      _ ≤ (Real.exp 1) ^ (6 * N + 1) := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hcard : (Fintype.card (ColumnDecoderCode N segments omitted imperfect) : ℝ) ≤
      (2 : ℝ) ^ (6 * N + 1) * (N : ℝ) ^ M := by
    exact_mod_cast card_columnDecoderCode_le N segments omitted imperfect
  calc
    _ ≤ (2 : ℝ) ^ (6 * N + 1) * (N : ℝ) ^ M := hcard
    _ ≤ Real.exp (6 * N + 1) * Real.exp ((M : ℝ) * Real.log N) := by
      rw [Real.exp_nat_mul, Real.exp_log hNpos]
      exact mul_le_mul_of_nonneg_right hbits (by positivity)
    _ = Real.exp ((6 * N + 1) + (M : ℝ) * Real.log N) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (52 * k) := by
      apply Real.exp_le_exp.mpr
      have hNbound : (N : ℝ) ≤ 4 * k := by exact_mod_cast hNk
      linarith

end TwoPointCorrelations

end OAI
