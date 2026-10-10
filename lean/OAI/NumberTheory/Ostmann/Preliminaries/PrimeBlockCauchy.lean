import OAI.NumberTheory.Ostmann.Preliminaries.Counting

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators

theorem prime_log_div_ge_terminal (p Q : ℕ) (hp : p.Prime) (hpQ : p ≤ Q)
    (hQ : 4 ≤ Q) : Real.log Q / (Q : ℝ) ≤ Real.log p / (p : ℝ) := by
  have hQr : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
  by_cases hp2 : p = 2
  · subst p
    have h := Real.log_div_self_antitoneOn
      (show Real.exp 1 ≤ (4 : ℝ) by linarith [Real.exp_one_lt_three])
      (show Real.exp 1 ≤ (Q : ℝ) by linarith [Real.exp_one_lt_three]) hQr
    have heq : Real.log (4 : ℝ) / 4 = Real.log (2 : ℝ) / 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      ring
    simpa only [heq, Nat.cast_ofNat] using h
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    exact Real.log_div_self_antitoneOn
      (show Real.exp 1 ≤ (p : ℝ) by linarith [Real.exp_one_lt_three])
      (show Real.exp 1 ≤ (Q : ℝ) by linarith [Real.exp_one_lt_three])
      (by exact_mod_cast hpQ)

theorem primeBlock_cauchy (Q : ℕ) (ν : ℕ → ℝ)
    (hν : ∀ p ∈ Q.primesLE, 0 < ν p) :
    (Nat.primeCounting Q : ℝ) ^ 2 ≤
      (∑ p ∈ Q.primesLE, ν p / p) * (∑ p ∈ Q.primesLE, (p : ℝ) / ν p) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Q.primesLE
    (r := fun _ => (1 : ℝ))
    (f := fun p => ν p / p) (g := fun p => (p : ℝ) / ν p)
    (fun p hp => div_nonneg (hν p hp).le (Nat.cast_nonneg _))
    (fun p hp => div_nonneg (Nat.cast_nonneg _) (hν p hp).le)
    (fun p hp => by
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.ne_zero
      have hv := (hν p hp).ne'
      field_simp; norm_num)
  simpa [Nat.primesLE_card_eq_primeCounting] using h

theorem primeBlock_weighted_cauchy (Q : ℕ) (ν : ℕ → ℝ) (hQ : 4 ≤ Q)
    (hν : ∀ p ∈ Q.primesLE, 0 < ν p) :
    (Real.log Q / (Q : ℝ)) * (Nat.primeCounting Q : ℝ) ^ 2 ≤
      (∑ p ∈ Q.primesLE, ν p / p) * (∑ p ∈ Q.primesLE, Real.log p / ν p) := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlog : 0 ≤ Real.log Q / (Q : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega))) hQpos.le
  have hterm (p : ℕ) (hp : p ∈ Q.primesLE) :
      (Real.log Q / (Q : ℝ)) * ((p : ℝ) / ν p) ≤ Real.log p / ν p := by
    have hp' := Nat.mem_primesLE.mp hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.2.ne_zero
    have h := mul_le_mul_of_nonneg_right
      (prime_log_div_ge_terminal p Q hp'.2 hp'.1 hQ)
      (div_nonneg (Nat.cast_nonneg p) (hν p hp).le)
    simpa only [div_mul_div_cancel₀ hp0] using h
  have hsum : (Real.log Q / (Q : ℝ)) *
      (∑ p ∈ Q.primesLE, (p : ℝ) / ν p) ≤
      ∑ p ∈ Q.primesLE, Real.log p / ν p := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hS : 0 ≤ ∑ p ∈ Q.primesLE, ν p / p :=
    Finset.sum_nonneg (fun p hp => div_nonneg (hν p hp).le (Nat.cast_nonneg p))
  calc
    _ ≤ (Real.log Q / (Q : ℝ)) *
        ((∑ p ∈ Q.primesLE, ν p / p) * (∑ p ∈ Q.primesLE, (p : ℝ) / ν p)) :=
      mul_le_mul_of_nonneg_left (primeBlock_cauchy Q ν hν) hlog
    _ = (∑ p ∈ Q.primesLE, ν p / p) *
        ((Real.log Q / (Q : ℝ)) * (∑ p ∈ Q.primesLE, (p : ℝ) / ν p)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hS

end Ostmann.Preliminaries

end OAI
