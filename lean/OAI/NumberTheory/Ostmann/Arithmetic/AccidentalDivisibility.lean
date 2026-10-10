import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.AccidentalDivisibility
open scoped BigOperators

theorem primeFactors_card_log_bound (N : ℕ) (hN : N ≠ 0) :
    (N.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log N := by
  have hpow : 2 ^ N.primeFactors.card ≤ N := by
    calc
      _ = ∏ _p ∈ N.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ N.primeFactors, p := Finset.prod_le_prod fun p hp =>
        (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.prod_primeFactors_dvd N)
  have hreal : (2:ℝ)^N.primeFactors.card ≤ (N:ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity : 0 < (2:ℝ)^N.primeFactors.card) hreal
  simpa only [Real.log_pow] using hlog

theorem weighted_prime_divisors (N : ℕ) (hN : N ≠ 0) (S : Finset ℕ)
    (μ : ℕ → ℝ) {α : ℝ} (hα : 0 ≤ α)
    (hbound : ∀ p ∈ S, μ p ≤ α) :
    (∑ p ∈ S with p.Prime ∧ p ∣ N, μ p) ≤
      α * (Real.log N / Real.log 2) := by
  have hcard : (S.filter fun p => p.Prime ∧ p ∣ N).card ≤ N.primeFactors.card := by
    apply Finset.card_le_card
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp hp).2.1,
      (Finset.mem_filter.mp hp).2.2,hN⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ ∑ _p ∈ S with _p.Prime ∧ _p ∣ N, α :=
      Finset.sum_le_sum fun p hp => hbound p (Finset.mem_filter.mp hp).1
    _ = ((S.filter fun p => p.Prime ∧ p ∣ N).card : ℝ) * α := by simp
    _ ≤ (N.primeFactors.card:ℝ)*α :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hα
    _ ≤ (Real.log N / Real.log 2)*α := by
      apply mul_le_mul_of_nonneg_right _ hα
      exact (le_div_iff₀ hlog2).2 (primeFactors_card_log_bound N hN)
    _ = _ := mul_comm _ _

theorem weighted_polynomial_roots {K : Type*} [CommRing K] [IsDomain K]
    [DecidableEq K] (P : Polynomial K) (hP : P ≠ 0) (S : Finset K)
    (μ : K → ℝ) {α : ℝ} (hα : 0 ≤ α) (hbound : ∀ x ∈ S, μ x ≤ α) :
    (∑ x ∈ S with P.eval x = 0, μ x) ≤ (P.natDegree:ℝ)*α := by
  have hcard : (S.filter fun x => P.eval x=0).card ≤ P.natDegree := by
    calc
      _ ≤ P.roots.toFinset.card := Finset.card_le_card fun x hx => by
        simpa [Polynomial.mem_roots hP, Polynomial.IsRoot] using
          (Finset.mem_filter.mp hx).2
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := P.card_roots'
  calc
    _ ≤ ∑ _x ∈ S with P.eval _x=0, α :=
      Finset.sum_le_sum fun x hx => hbound x (Finset.mem_filter.mp hx).1
    _ = ((S.filter fun x => P.eval x=0).card:ℝ)*α := by simp
    _ ≤ (P.natDegree:ℝ)*α :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hα

end Ostmann.Arithmetic.AccidentalDivisibility

end

end OAI
