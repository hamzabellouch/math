import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedCompressionSource

namespace OAI

/-! # Paying for all stopped compression joins with the source ledger -/

namespace LowSpaceSubsetSum.CompressionData

open scoped BigOperators
variable {n : ℕ} (D : CompressionData n)

theorem sum_pass_allowance (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (he : D.compactTests e = true) :
    (∑ z, BudgetedCompressionPass.allowance D.input (compressionDictionaryCapacity n) B
      (D.passData e q z)) ≤ inputScale D.input ^ 5 * (D.trialLedger B e q).queries +
        B * (D.trialLedger B e q).copies + 16 * q.val := by
  have h := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (Fin q.val))) =>
    D.pass_allowance B e q z he)
  simpa only [trialLedger, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm q.val 16] using h

theorem sum_pass_allowance_scale (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (he : D.compactTests e = true) (hn : 10000 ≤ n) :
    (∑ z, BudgetedCompressionPass.allowance D.input (compressionDictionaryCapacity n) B
      (D.passData e q z)) ≤ inputScale D.input ^ 6 * 2 ^ ((n + 1) / 2) := by
  let T := 2 ^ ((n + 1) / 2)
  have hpow : (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (T : ℝ) := by
    change (2 : ℝ) ^ ((n : ℝ) / 2) ≤ ((2 ^ ((n + 1) / 2) : ℕ) : ℝ)
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hh : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 2 * ((n + 1) / 2) by omega)
    linarith
  have hl := D.trialLedger_half_exponential B e q (by omega)
  have hqueries : (D.trialLedger B e q).queries ≤ 30 * T := by
    have h := hl.1.trans (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 30))
    exact_mod_cast h
  have hcopies : B * (D.trialLedger B e q).copies ≤ 4 * T := by
    have h := hl.2.2.1.trans (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4))
    exact_mod_cast h
  have hprime : q.val ≤ T := by
    apply (Nat.le_of_mem_primesLE (Finset.mem_filter.mp q.property).1).trans
    apply Nat.pow_le_pow_right (by decide)
    unfold compressionPrimeExponent
    omega
  have hu : 10000 ≤ inputScale D.input := by unfold inputScale; omega
  have hu5 : 1 ≤ inputScale D.input ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hcoef : 30 * inputScale D.input ^ 5 + 20 ≤ inputScale D.input ^ 6 := by
    have hh : 50 * inputScale D.input ^ 5 ≤ inputScale D.input ^ 6 := by
      calc
        _ ≤ inputScale D.input * inputScale D.input ^ 5 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := (pow_succ' _ _).symm
    omega
  calc
    _ ≤ inputScale D.input ^ 5 * (D.trialLedger B e q).queries +
        B * (D.trialLedger B e q).copies + 16 * q.val := D.sum_pass_allowance B e q he
    _ ≤ (30 * inputScale D.input ^ 5 + 20) * T := by
      have hmul := Nat.mul_le_mul_left (inputScale D.input ^ 5) hqueries
      have hq := Nat.mul_le_mul_left 16 hprime
      nlinarith only [hmul, hcopies, hq]
    _ ≤ inputScale D.input ^ 6 * T := Nat.mul_le_mul_right T hcoef

end LowSpaceSubsetSum.CompressionData

end OAI
