import Mathlib

namespace OAI
open scoped BigOperators

namespace Problem337

/-- A dyadic prime block contributes at most a constant divided by its
logarithmic index. This uses only the elementary Chebyshev upper bound. -/
theorem prime_reciprocal_dyadic_block (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE (2 ^ (n + 1)) \ Nat.primesLE (2 ^ n),
      (1 : ℝ) / p ≤ 4 / (n : ℝ) := by
  let s := Nat.primesLE (2 ^ (n + 1)) \ Nat.primesLE (2 ^ n)
  let A : ℝ := (2 : ℝ) ^ n * ((n : ℝ) * Real.log 2)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  have hpdata : ∀ p ∈ s, p.Prime ∧ 2 ^ n < p := by
    intro p hp
    obtain ⟨hp, hnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpbound, hpprime⟩ := Nat.mem_primesLE.mp hp
    refine ⟨hpprime, ?_⟩
    by_contra h
    exact hnot (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
  have hterms : ∀ p ∈ s, (1 : ℝ) / p ≤ Real.log p / A := by
    intro p hp
    have hpdata' := hpdata p hp
    have hp : (0 : ℝ) < p := by exact_mod_cast hpdata'.1.pos
    have hple : (2 : ℝ) ^ n ≤ p := by exact_mod_cast hpdata'.2.le
    have hlogp : (n : ℝ) * Real.log 2 ≤ Real.log p := by
      calc
        (n : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ n) := (Real.log_pow _ _).symm
        _ ≤ Real.log p := Real.log_le_log (by positivity) hple
    apply (div_le_div_iff₀ hp hA).mpr
    simp only [one_mul]
    dsimp [A]
    nlinarith [mul_le_mul hple hlogp (by positivity : 0 ≤ (n : ℝ) * Real.log 2)
      hp.le]
  have hlogs : ∑ p ∈ s, Real.log (p : ℝ) ≤
      Chebyshev.theta (2 ^ (n + 1) : ℕ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)
  have htheta := Chebyshev.theta_le_log4_mul_x
    (show (0 : ℝ) ≤ (2 ^ (n + 1) : ℕ) by positivity)
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := Real.log_pow _ _
  change (∑ p ∈ s, (1 : ℝ) / p) ≤ _
  calc
    ∑ p ∈ s, (1 : ℝ) / p ≤ ∑ p ∈ s, Real.log (p : ℝ) / A :=
      Finset.sum_le_sum hterms
    _ = (∑ p ∈ s, Real.log (p : ℝ)) / A := (Finset.sum_div _ _ _).symm
    _ ≤ Chebyshev.theta (2 ^ (n + 1) : ℕ) / A :=
      div_le_div_of_nonneg_right hlogs hA.le
    _ ≤ (Real.log 4 * (2 ^ (n + 1) : ℕ)) / A :=
      div_le_div_of_nonneg_right htheta hA.le
    _ = 4 / (n : ℝ) := by
      push_cast
      simp only [pow_succ, hfour, A]
      field_simp
      ring

/-- Summing dyadic blocks gives a harmonic majorant for prime reciprocals. -/
theorem prime_reciprocal_two_pow (n : ℕ) :
    ∑ p ∈ Nat.primesLE (2 ^ n), (1 : ℝ) / p ≤ 8 * (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      norm_num [Nat.primesLE_eq_filter_Icc_two, harmonic, Finset.filter_singleton, Nat.prime_two]
    have hn1 : 1 ≤ n := by omega
    have hblock := prime_reciprocal_dyadic_block n hn1
    have hsubset : Nat.primesLE (2 ^ n) ⊆ Nat.primesLE (2 ^ (n + 1)) :=
      Nat.primesLE_mono (Nat.pow_le_pow_right (by omega) (by omega))
    have hsplit := Finset.sum_sdiff (f := fun p : ℕ => (1 : ℝ) / p) hsubset
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hfrac : (4 : ℝ) / n ≤ 8 / (n + 1 : ℕ) := by
      apply (div_le_div_iff₀ hnpos (by positivity)).mpr
      norm_cast
      omega
    have hhar : (harmonic (n + 1) : ℝ) = harmonic n + 1 / (n + 1 : ℕ) := by
      simp [harmonic_succ, one_div]
    rw [hhar]
    simp only [div_eq_mul_inv] at hblock hfrac hsplit ih ⊢
    linarith

/-- A direct logarithmic majorant, with the binary logarithm only in the
argument of the outside logarithm. -/
theorem prime_reciprocal_log_bound (T : ℕ) :
    ∑ p ∈ Nat.primesLE T, (1 : ℝ) / p ≤
      8 * (1 + Real.log ((Nat.log 2 T + 1 : ℕ) : ℝ)) := by
  have hT : T ≤ 2 ^ (Nat.log 2 T + 1) :=
    (Nat.lt_pow_succ_log_self (by omega : 1 < 2) T).le
  calc
    ∑ p ∈ Nat.primesLE T, (1 : ℝ) / p ≤
        ∑ p ∈ Nat.primesLE (2 ^ (Nat.log 2 T + 1)), (1 : ℝ) / p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono hT)
      intro p _ _
      positivity
    _ ≤ 8 * (harmonic (Nat.log 2 T + 1) : ℝ) := prime_reciprocal_two_pow _
    _ ≤ 8 * (1 + Real.log ((Nat.log 2 T + 1 : ℕ) : ℝ)) := by
      gcongr
      exact harmonic_le_one_add_log _

/-- An elementary uniform `O(log log T)` bound for reciprocal primes. -/
theorem sum_prime_reciprocals_le_loglog (T : ℕ) (hT : 2 ≤ T) :
    ∑ p ∈ Nat.primesLE T, (1 : ℝ) / p ≤
      56 * Real.log (1 + Real.log (T : ℝ)) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hTzero : T ≠ 0 := by omega
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  have hlogtwo' : Real.log 2 ≤ (1 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    exact this
  have hlogT : (1 / 2 : ℝ) ≤ Real.log (T : ℝ) :=
    hlogtwo.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hT))
  have hnlog : (Nat.log 2 T : ℝ) * Real.log 2 ≤ Real.log (T : ℝ) := by
    calc
      _ = Real.log ((2 : ℝ) ^ Nat.log 2 T) := (Real.log_pow _ _).symm
      _ ≤ Real.log (T : ℝ) := Real.log_le_log (by positivity)
        (by exact_mod_cast Nat.pow_log_le_self 2 hTzero)
  have hnnonneg : (0 : ℝ) ≤ Nat.log 2 T := by positivity
  have hindex : ((Nat.log 2 T + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log (T : ℝ)) := by
    push_cast
    nlinarith
  have hy : (1 / 3 : ℝ) ≤ Real.log (1 + Real.log (T : ℝ)) := by
    have hthree : (1 / 3 : ℝ) ≤ Real.log (3 / 2 : ℝ) := by
      have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
      norm_num at this ⊢
      exact this
    exact hthree.trans (Real.log_le_log (by norm_num) (by linarith))
  have hindexlog : Real.log ((Nat.log 2 T + 1 : ℕ) : ℝ) ≤
      1 + Real.log (1 + Real.log (T : ℝ)) := by
    calc
      _ ≤ Real.log (2 * (1 + Real.log (T : ℝ))) :=
        Real.log_le_log (by positivity) hindex
      _ = Real.log 2 + Real.log (1 + Real.log (T : ℝ)) :=
        Real.log_mul (by norm_num) (by linarith)
      _ ≤ 1 + Real.log (1 + Real.log (T : ℝ)) := by linarith
  have hh := prime_reciprocal_log_bound T
  linarith

end Problem337

end OAI
