import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3

private theorem base_rank_denominator_bound (s D : ℕ) {p : ℝ}
    (hD : (D : ℝ) ≤ p) :
    4 * (((D + 1) * (s + 1) ^ D : ℕ) : ℝ) ≤
      Real.exp (p + 5 + p * (s + 1)) := by
  have hs : (s + 1 : ℝ) ≤ Real.exp (s + 1) :=
    (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)).trans
      (Real.add_one_le_exp (s + 1))
  have hpow : ((s + 1 : ℕ) : ℝ) ^ D ≤ Real.exp (p * (s + 1)) := by
    calc
      _ ≤ (Real.exp (s + 1)) ^ D :=
        pow_le_pow_left₀ (by positivity) (by simpa only [Nat.cast_add, Nat.cast_one] using hs) D
      _ = Real.exp ((D : ℝ) * (s + 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hD (by positivity))
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hdim : (D + 1 : ℝ) ≤ Real.exp (p + 1) := by
    have hh := Real.add_one_le_exp (p + 1)
    linarith
  calc
    _ = (4 * (D + 1 : ℝ)) * ((s + 1 : ℕ) : ℝ) ^ D := by push_cast; ring
    _ ≤ (Real.exp 4 * Real.exp (p + 1)) * Real.exp (p * (s + 1)) :=
      mul_le_mul (mul_le_mul hfour hdim (by positivity) (Real.exp_nonneg _))
        hpow (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem exists_unconditionedBaseRetention_power_budget (s n E H : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ (p : ℝ), 2 ≤ p →
      let b := (p + 2) ^ A
      p + 2 ≤ b ∧ (((p + n + 4) ^ E + 2) ^ H ≤ b) ∧
      Real.exp (-b) ≤ Real.exp (-((p + n + 4) ^ E)) ∧
      ∀ D : ℕ, D ≤ ⌊p⌋₊ →
        Real.exp (-b) ≤
          ((Real.exp (-p) / 4) / (((D + 1) * (s + 1) ^ D : ℕ) : ℝ)) *
            Real.exp (-((p + n + 4) ^ E)) := by
  let depth : Polynomial ℕ := (Polynomial.X + Polynomial.C (n + 4)) ^ E
  let complexity : Polynomial ℕ := (depth + 2) ^ H
  let massLog : Polynomial ℕ :=
    2 * Polynomial.X + 5 + Polynomial.X * Polynomial.C (s + 1) + depth
  obtain ⟨A, hA, hbudget⟩ :=
    exists_natPolynomial_fixed_power_budget (Polynomial.X + 2 + complexity + massLog)
  refine ⟨A, hA, ?_⟩
  intro p hp b
  let B := (p + n + 4) ^ E
  let T := 2 * p + 5 + p * (s + 1) + B
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hbudget' : p + 2 + (B + 2) ^ H + T ≤ b := by
    simpa [depth, complexity, massLog, Polynomial.eval₂_pow, B, T, b,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using hbudget p hp0
  have hpb : p + 2 ≤ b := by nlinarith [pow_nonneg (by linarith : 0 ≤ B + 2) H]
  have hCb : (B + 2) ^ H ≤ b := by linarith
  have hTb : T ≤ b := by nlinarith [pow_nonneg (by linarith : 0 ≤ B + 2) H]
  have hBb : B ≤ b := by
    have hBT : B ≤ T := by
      dsimp only [T]
      nlinarith [mul_nonneg hp0 (show 0 ≤ (s : ℝ) + 1 by positivity)]
    exact hBT.trans hTb
  refine ⟨hpb, hCb, Real.exp_le_exp.mpr (neg_le_neg hBb), ?_⟩
  intro D hD
  have hDr : (D : ℝ) ≤ p :=
    (Nat.cast_le.mpr hD).trans (Nat.floor_le hp0)
  let denominator : ℝ := (((D + 1) * (s + 1) ^ D : ℕ) : ℝ)
  have hd0 : 0 < denominator := by dsimp only [denominator]; positivity
  have hden : 4 * denominator ≤ Real.exp (p + 5 + p * (s + 1)) :=
    base_rank_denominator_bound s D hDr
  have hlower : Real.exp (-T) ≤ (Real.exp (-p) / 4 / denominator) * Real.exp (-B) := by
    rw [div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 4 * denominator)]
    calc
      _ ≤ Real.exp (-T) * Real.exp (p + 5 + p * (s + 1)) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
      _ = Real.exp (-p) * Real.exp (-B) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp only [T]
        ring
  exact (Real.exp_le_exp.mpr (neg_le_neg hTb)).trans hlower

end Erdos3

end

end OAI
