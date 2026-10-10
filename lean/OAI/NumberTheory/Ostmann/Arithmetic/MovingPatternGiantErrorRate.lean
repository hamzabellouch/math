import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternCostRate

namespace OAI

/-! # The giant comparison error after the actual coefficient mass -/

namespace Ostmann
open Filter

/-- The upper prime cutoff costs one factor per internal class. Even at the
full permitted small-prime scale, the two giant errors remain negligible. -/
theorem movingPattern_giant_error_rate (n : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ c : ℕ, c ≤ 4 * n * 2 ^ n → ∀ E U : ℝ,
      0 ≤ E → E ≤ Real.exp (C * L) → 0 ≤ U → U ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) →
      ((2 : ℝ) ^ c * E ^ (4 * n * 2 ^ n - c) * U ^ c) *
        (Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
          Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))) ≤
        Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  let J := 4 * n * 2 ^ n
  let K : ℝ := ((J ^ 2 + J : ℕ) : ℝ) * C
  let H : ℝ := K + J + 1
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  filter_upwards [arithmetic_error_absorption (12 / 1000) (1225 / 100000) (2 / 1000)
    H 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L herr hL c hc E U hE hEC hU hUC
  have hL0 : 0 ≤ L := by linarith
  have hExp : 1 ≤ Real.exp ((12 / 1000 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hprior : (2 : ℝ) ^ c * E ^ (J - c) ≤ Real.exp (K * L) := by
    calc
      _ ≤ (max 2 E) ^ J := movingPattern_loss_le n c hc E hE
      _ ≤ (max 2 (Real.exp (C * L))) ^ J :=
        pow_le_pow_left₀ (by positivity) (max_le_max_left _ hEC) J
      _ ≤ (2 : ℝ) ^ (J ^ 2) * (max 2 (Real.exp (C * L))) ^ J :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
      _ ≤ _ := movingPattern_total_cost_le_exp n C L hC hL
  have hU' : U ^ c ≤ Real.exp ((J : ℝ) * Real.exp ((12 / 1000 : ℝ) * L)) := by
    calc
      _ ≤ (Real.exp (Real.exp ((12 / 1000 : ℝ) * L))) ^ c := pow_le_pow_left₀ hU hUC c
      _ ≤ (Real.exp (Real.exp ((12 / 1000 : ℝ) * L))) ^ J :=
        pow_le_pow_right₀ (Real.one_le_exp_iff.mpr (Real.exp_pos _).le) hc
      _ = _ := (Real.exp_nat_mul _ J).symm
  let mass := (2 : ℝ) ^ c * E ^ (J - c) * U ^ c
  have hmass0 : 0 ≤ mass := by dsimp only [mass]; positivity
  have hmass : mass ≤ Real.exp (K * L + (J : ℝ) * Real.exp ((12 / 1000 : ℝ) * L)) := by
    simpa only [Real.exp_add] using mul_le_mul hprior hU' (pow_nonneg hU _) (Real.exp_nonneg _)
  have htwo : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hdouble : 2 * mass ≤ Real.exp (H * L + H * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    apply (mul_le_mul htwo hmass hmass0 (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hJL : (J : ℝ) ≤ (J : ℝ) * L := le_mul_of_one_le_right (Nat.cast_nonneg _) hL
    have hHJ : (J : ℝ) ≤ H := by dsimp only [H]; linarith
    have hJHL : (J : ℝ) ≤ H * L := hJL.trans (mul_le_mul_of_nonneg_right hHJ hL0)
    have he := mul_le_mul_of_nonneg_right hJHL (Real.exp_nonneg ((12 / 1000 : ℝ) * L))
    dsimp only [H] at *
    nlinarith
  have hsmall : Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) ≤
      Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
    apply Real.exp_le_exp.mpr
    have hh : (1225 / 100000 : ℝ) * L ≤ (125 / 10000 : ℝ) * L := by linarith
    linarith [Real.exp_le_exp.mpr hh]
  change mass * _ ≤ _
  calc
    _ ≤ (2 * mass) * Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
      have h := mul_le_mul_of_nonneg_left hsmall hmass0
      nlinarith only [h]
    _ ≤ _ := (mul_le_mul_of_nonneg_right hdouble (Real.exp_nonneg _)).trans
      (by simpa only [pow_one, one_mul, neg_mul] using herr)

end Ostmann

end OAI
