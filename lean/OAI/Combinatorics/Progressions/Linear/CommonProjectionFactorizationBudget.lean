import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

theorem exists_commonProjectionFactorization_budget (A B : ℕ) (hA : 2 ≤ A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + A) ^ A
      p ≤ q ∧ 0 ≤ q ∧ (q + 2) ^ B ≤ (p + C) ^ C ∧
        ((q + 2) ^ 2 + 2) ^ 63 + 1 ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  let P : Polynomial ℕ := (Q + 2) ^ B + (((Q + 2) ^ 2 + 2) ^ 63 + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  let q : ℝ := (p + A) ^ A
  have hbase : 1 ≤ p + A := by
    have : (2 : ℝ) ≤ A := by exact_mod_cast hA
    linarith
  have hpq : p ≤ q := by
    apply (le_add_of_nonneg_right (Nat.cast_nonneg A)).trans
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ A by omega)
  have hq : 0 ≤ q := hp.trans hpq
  have hfirst : 0 ≤ (q + 2) ^ B := by positivity
  have hsecond : 0 ≤ ((q + 2) ^ 2 + 2) ^ 63 + 1 := by positivity
  have hsum : (q + 2) ^ B + (((q + 2) ^ 2 + 2) ^ 63 + 1) ≤ (p + C) ^ C := by
    simpa [P, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨hpq, hq, (le_add_of_nonneg_right hsecond).trans hsum,
    (le_add_of_nonneg_left hfirst).trans hsum⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
