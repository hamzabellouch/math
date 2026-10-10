import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRowNorm
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeDivisors

namespace OAI

/-! # Incidence losses in prime dilation are only logarithmic -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_prime_incidence {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {n B : ℕ} (hn : 0 < n) (hnB : n ≤ B) :
    (P.filter (fun p => p ∣ n)).card ≤ Nat.log 2 B := by
  let Q := P.filter (fun p => p ∣ n)
  have hsub : Q ⊆ n.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hP p (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2, Nat.ne_of_gt hn⟩
  have hd : (∏ p ∈ Q, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset Q n.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd n)
  have hpow : 2 ^ Q.card ≤ n := by
    calc
      _ = ∏ _p ∈ Q, 2 := by simp
      _ ≤ ∏ p ∈ Q, p := Finset.prod_le_prod (fun p hp => (hP p (Finset.mem_filter.mp hp).1).two_le)
      _ ≤ n := Nat.le_of_dvd hn hd
  exact Nat.le_log_of_pow_le (by norm_num) (hpow.trans hnB)

theorem quadratic_prime_restricted_energy {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (N : ℕ) (v : ℕ → ℂ) :
    (∑ p ∈ P, quadraticSieveEnergy N (fun n => if p ∣ n then v n else 0)) ≤
      (Nat.log 2 N : ℝ) * quadraticSieveEnergy N v := by
  unfold quadraticSieveEnergy
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hcount := quadratic_prime_incidence hP hi.1 hi.2
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (sq_nonneg _)

theorem quadratic_prime_bad_rows {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {B : ℕ} (hS : ∀ m ∈ S, 0 < m ∧ m ≤ B) (N : ℕ) (v : ℕ → ℂ) :
    (∑ p ∈ P, ∑ m ∈ S.filter (fun m => p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2) ≤
      (Nat.log 2 B : ℝ) * quadraticRowEnergy S N v := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold quadraticRowEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hcount := quadratic_prime_incidence hP (hS m hm).1 (hS m hm).2
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (sq_nonneg _)

end Ostmann

end OAI
