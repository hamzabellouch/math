import OAI.NumberTheory.TwoPoint.Walks.RankDecay

namespace OAI

/-! The finite choice of perfect rows, lit designation and offending column
is negligible compared with the rank saving. -/

namespace TwoPointCorrelations

open Filter

lemma rank_slice_cost_bound (L Cj : ℝ) (R J : ℕ) (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log L) (hCj : 0 ≤ Cj)
    (hR : (R : ℝ) ≤ 2 * L) (hJ : (J : ℝ) ≤ Cj * Real.log L) :
    (2 : ℝ) ^ (R * J) * 2 ^ R * J ≤
      Real.exp ((3 * Cj + 2) * L * (Real.log L) ^ 2) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hJexp : (J : ℝ) ≤ Real.exp J := by linarith [Real.add_one_le_exp (J : ℝ)]
  have hprod : ((R * J : ℕ) : ℝ) ≤ 2 * Cj * L * Real.log L := by
    push_cast
    exact (mul_le_mul hR hJ (Nat.cast_nonneg _) (by positivity)).trans_eq (by ring)
  have hl : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
  have hl1 : (1 : ℝ) ≤ (Real.log L) ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * Cj * L by positivity)
  have h2 := mul_le_mul_of_nonneg_left hl1 (show 0 ≤ 2 * L by positivity)
  have h3 : (J : ℝ) ≤ Cj * L * (Real.log L) ^ 2 := by
    calc
      _ ≤ Cj * Real.log L := hJ
      _ ≤ Cj * (Real.log L) ^ 2 := mul_le_mul_of_nonneg_left hl hCj
      _ ≤ _ := by nlinarith [mul_nonneg hCj (sq_nonneg (Real.log L))]
  calc
    _ ≤ (Real.exp 1) ^ (R * J) * (Real.exp 1) ^ R * Real.exp J :=
      mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by norm_num) htwo _)
        (pow_le_pow_left₀ (by norm_num) htwo _) (by positivity) (by positivity))
        hJexp (by positivity) (by positivity)
    _ = Real.exp (((R * J : ℕ) : ℝ) + R + J) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem eventually_rank_slice_decay (Cj : ℝ) (hCj : 0 ≤ Cj) :
    ∀ᶠ L : ℝ in atTop, ∀ R J : ℕ,
      (R : ℝ) ≤ 2 * L → (J : ℝ) ≤ Cj * Real.log L →
      ((2 : ℝ) ^ (R * J) * 2 ^ R * J) *
        Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  have hgap := (tendsto_rpow_atTop (show 0 < (1 / 200 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 16)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_crude_cost_small (2 * (3 * Cj + 2)) (by positivity), hgap]
    with L hL hlog hcost hgap
  intro R J hR hJ
  have hLp : 0 < L := by linarith
  have hsmall : (3 * Cj + 2) * L * (Real.log L) ^ 2 ≤
      (1 / 16 : ℝ) * L ^ (203 / 200 : ℝ) := by nlinarith
  have hpower : L ^ (101 / 100 : ℝ) * L ^ (1 / 200 : ℝ) =
      L ^ (203 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hgap' := mul_le_mul_of_nonneg_left hgap
    (Real.rpow_nonneg hLp.le (101 / 100 : ℝ))
  rw [hpower] at hgap'
  calc
    _ ≤ Real.exp ((3 * Cj + 2) * L * (Real.log L) ^ 2) *
        Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) :=
      mul_le_mul_of_nonneg_right (rank_slice_cost_bound L Cj R J hL hlog hCj hR hJ) (by positivity)
    _ = Real.exp ((3 * Cj + 2) * L * (Real.log L) ^ 2 -
        (1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end TwoPointCorrelations

end OAI
