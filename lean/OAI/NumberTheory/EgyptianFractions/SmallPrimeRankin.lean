import OAI.NumberTheory.EgyptianFractions.SubcriticalPowerSum
import OAI.NumberTheory.EgyptianFractions.SmoothRankin

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.DivisorMoment

/-- The small-prime smooth-prefix tail estimate from the divisor-moment proof.
The constant is absolute and the finite set of prefixes is arbitrary. -/
theorem small_prime_smooth_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S v : ℝ), 1 ≤ S → ∀ (N : ℕ),
      (N : ℝ) ≤ S ^ (4 : ℕ) + 1 → ∀ s : Finset ℕ,
      (∀ n ∈ s, n ∈ N.smoothNumbers) →
      (∀ n ∈ s, Real.exp (v / 5) ≤ (n : ℝ)) →
      (∑ n ∈ s, (1 : ℝ) / n) ≤ Real.exp (-v / 50 + C * S ^ (2 / 5 : ℝ)) := by
  obtain ⟨C, hC, hprodlog⟩ := small_prime_rankin_product_log_bound
  refine ⟨C, hC, ?_⟩
  intro S v hS N hN s hs hlarge
  have hprimes : ∀ p ∈ N.primesBelow, 2 ≤ p ∧ (p : ℝ) ≤ S ^ (4 : ℕ) := by
    intro p hp
    refine ⟨(Nat.prime_of_mem_primesBelow hp).two_le, ?_⟩
    have hpN := Nat.lt_of_mem_primesBelow hp
    have hpR : (p : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hpN
    linarith
  have hrpow (p : ℕ) (hp : p ∈ N.primesBelow) :
      0 ≤ (p : ℝ) ^ (-(9 / 10 : ℝ)) ∧ (p : ℝ) ^ (-(9 / 10 : ℝ)) < 1 := by
    refine ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_⟩
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have hprodpos : 0 < ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-(9 / 10 : ℝ)))⁻¹ := by
    apply Finset.prod_pos
    intro p hp
    exact inv_pos.mpr (sub_pos.mpr (hrpow p hp).2)
  have hprod : (∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-(9 / 10 : ℝ)))⁻¹) ≤
      Real.exp (C * S ^ (2 / 5 : ℝ)) :=
    (Real.log_le_iff_le_exp hprodpos).mp (hprodlog S hS N.primesBelow hprimes)
  have heuler : (∏ p ∈ N.primesBelow, ∑' j : ℕ,
      ((j + 1 : ℕ) : ℝ) ^ (0 : ℕ) * ((p : ℝ) ^ ((1 / 10 : ℝ) - 1)) ^ j) =
      ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-(9 / 10 : ℝ)))⁻¹ := by
    apply Finset.prod_congr rfl
    intro p hp
    norm_num only [pow_zero, one_mul, show (1 / 10 : ℝ) - 1 = -(9 / 10 : ℝ) by norm_num]
    exact tsum_geometric_of_lt_one (hrpow p hp).1 (hrpow p hp).2
  have htail := Problem337.divisor_smooth_rankin_bound 0
    (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num : (1 / 10 : ℝ) < 1)
    N s hs hlarge
  simp only [pow_zero] at htail heuler
  rw [heuler] at htail
  calc
    (∑ n ∈ s, (1 : ℝ) / n) ≤ Real.exp (-(1 / 10 : ℝ) * (v / 5)) *
        ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-(9 / 10 : ℝ)))⁻¹ := htail
    _ ≤ Real.exp (-(1 / 10 : ℝ) * (v / 5)) * Real.exp (C * S ^ (2 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-v / 50 + C * S ^ (2 / 5 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- A cutoff phrased directly in terms of prime factors, without a smooth-number index. -/
theorem small_prime_factor_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S v : ℝ), 1 ≤ S → ∀ s : Finset ℕ,
      (∀ n ∈ s, ∀ p ∈ n.primeFactorsList, (p : ℝ) < S ^ (4 : ℕ)) →
      (∀ n ∈ s, Real.exp (v / 5) ≤ (n : ℝ)) →
      (∑ n ∈ s, (1 : ℝ) / n) ≤ Real.exp (-v / 50 + C * S ^ (2 / 5 : ℝ)) := by
  obtain ⟨C, hC, htail⟩ := small_prime_smooth_tail_bound
  refine ⟨C, hC, ?_⟩
  intro S v hS s hprime hlarge
  apply htail S v hS ⌈S ^ (4 : ℕ)⌉₊
    (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ S ^ (4 : ℕ))).le s
  · intro n hn
    apply Nat.mem_smoothNumbers.mpr
    refine ⟨?_, ?_⟩
    · have hnpos : 0 < (n : ℝ) := (Real.exp_pos _).trans_le (hlarge n hn)
      exact_mod_cast hnpos.ne'
    · intro p hp
      exact Nat.lt_ceil.mpr (hprime n hn p hp)
  · exact hlarge

end Problem337.DivisorMoment

end

end OAI
