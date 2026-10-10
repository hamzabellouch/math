import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Problem337

/-- Chebyshev's thirty-periodic floor combination takes only the values zero
and one. This is the finite arithmetic behind the improved lower constant. -/
theorem chebyshev_thirty_weight_bounds (n : ℕ) :
    0 ≤ (n : ℤ) - (n / 2 : ℕ) - (n / 3 : ℕ) - (n / 5 : ℕ) + (n / 30 : ℕ) ∧
    (n : ℤ) - (n / 2 : ℕ) - (n / 3 : ℕ) - (n / 5 : ℕ) + (n / 30 : ℕ) ≤ 1 := by
  omega

/-- The factorial logarithm is a finite Mangoldt sum with floor weights;
the outer range may be any larger initial interval. -/
theorem log_factorial_eq_sum_mangoldt_div {m N : ℕ} (hm : m ≤ N) :
    Real.log (m.factorial : ℝ) =
      ∑ d ∈ Finset.range (N + 1), Λ d * ((m / d : ℕ) : ℝ) := by
  classical
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod,
    Real.log_prod (by intro i hi; positivity)]
  calc
    (∑ i ∈ Finset.range m, Real.log ((i + 1 : ℕ) : ℝ)) =
        ∑ i ∈ Finset.range m, ∑ d ∈ Finset.range (N + 1),
          if d ∣ i + 1 then Λ d else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiN : i + 1 ≤ N := (Finset.mem_range.mp hi |> Nat.succ_le_of_lt).trans hm
      have he : (Finset.range (N + 1)).filter (fun d => d ∣ i + 1) =
          (i + 1).divisors := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
        constructor
        · intro h
          exact ⟨h.2, by omega⟩
        · intro h
          exact ⟨by have := Nat.le_of_dvd (by omega : 0 < i + 1) h.1; omega, h.1⟩
      rw [← Finset.sum_filter, he, ArithmeticFunction.vonMangoldt_sum]
    _ = ∑ d ∈ Finset.range (N + 1), ∑ i ∈ Finset.range m,
          if d ∣ i + 1 then Λ d else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter, Finset.sum_const, Nat.card_multiples]
      simp [mul_comm]

/-- An explicit elementary lower bound for `ψ`, stronger asymptotically
than the single central-binomial-coefficient bound. -/
theorem chebyshev_psi_ge_factorial_combination (N : ℕ) :
    Real.log (N.factorial : ℝ) - Real.log ((N / 2).factorial : ℝ) -
      Real.log ((N / 3).factorial : ℝ) - Real.log ((N / 5).factorial : ℝ) +
      Real.log ((N / 30).factorial : ℝ) ≤ Chebyshev.psi N := by
  rw [log_factorial_eq_sum_mangoldt_div (le_refl N),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 2),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 3),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 5),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 30)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have hpsi : Chebyshev.psi N = ∑ d ∈ Finset.range (N + 1), Λ d := by
    simp [Chebyshev.psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]
  rw [hpsi]
  apply Finset.sum_le_sum
  intro d hd
  have hw := (chebyshev_thirty_weight_bounds (N / d)).2
  have hdiv (k : ℕ) : N / k / d = N / d / k := by
    simp [Nat.div_div_eq_div_mul, Nat.mul_comm]
  simp_rw [hdiv]
  have hn : N / d + N / d / 30 ≤ N / d / 2 + N / d / 3 + N / d / 5 + 1 := by
    omega
  have hnR : ((N / d : ℕ) : ℝ) + (N / d / 30 : ℕ) ≤
      (N / d / 2 : ℕ) + (N / d / 3 : ℕ) + (N / d / 5 : ℕ) + 1 := by
    exact_mod_cast hn
  nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := d)]

/-- The same factorial lower bound at real endpoints, ready for asymptotic
use without any rounding or integrality hypothesis. -/
theorem chebyshev_psi_ge_floor_factorial_combination (x : ℝ) :
    Real.log (⌊x⌋₊.factorial : ℝ) - Real.log (⌊x / 2⌋₊.factorial : ℝ) -
      Real.log (⌊x / 3⌋₊.factorial : ℝ) - Real.log (⌊x / 5⌋₊.factorial : ℝ) +
      Real.log (⌊x / 30⌋₊.factorial : ℝ) ≤ Chebyshev.psi x := by
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  simpa only [Nat.floor_div_ofNat] using
    chebyshev_psi_ge_factorial_combination ⌊x⌋₊

/-- Extending a Mangoldt prefix to a larger range by an indicator. -/
theorem chebyshev_psi_nat_sum_indicator {m N : ℕ} (hm : m ≤ N) :
    Chebyshev.psi m = ∑ d ∈ Finset.range (N + 1), if d ≤ m then Λ d else 0 := by
  classical
  rw [← Finset.sum_filter]
  have hs : (Finset.range (N + 1)).filter (fun d => d ≤ m) = Finset.range (m + 1) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hs]
  simp [Chebyshev.psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]

/-- The complementary upper recurrence from the same thirty-periodic
kernel. Iteration gives the classical upper Chebyshev constant `6C/5`. -/
theorem chebyshev_psi_le_factorial_combination_add (N : ℕ) :
    Chebyshev.psi N ≤
      Real.log (N.factorial : ℝ) - Real.log ((N / 2).factorial : ℝ) -
        Real.log ((N / 3).factorial : ℝ) - Real.log ((N / 5).factorial : ℝ) +
        Real.log ((N / 30).factorial : ℝ) + Chebyshev.psi (N / 6 : ℕ) := by
  rw [log_factorial_eq_sum_mangoldt_div (le_refl N),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 2),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 3),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 5),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 30),
    chebyshev_psi_nat_sum_indicator (Nat.div_le_self N 6)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hpsi : Chebyshev.psi N = ∑ d ∈ Finset.range (N + 1), Λ d := by
    simp [Chebyshev.psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]
  rw [hpsi]
  apply Finset.sum_le_sum
  intro d hd
  have hdiv (k : ℕ) : N / k / d = N / d / k := by
    simp [Nat.div_div_eq_div_mul, Nat.mul_comm]
  simp_rw [hdiv]
  by_cases hsmall : d ≤ N / 6
  · rw [ite_eq_left hsmall]
    have hw := (chebyshev_thirty_weight_bounds (N / d)).1
    have hn : N / d / 2 + N / d / 3 + N / d / 5 ≤ N / d + N / d / 30 := by
      omega
    have hnR : ((N / d / 2 : ℕ) : ℝ) + (N / d / 3 : ℕ) + (N / d / 5 : ℕ) ≤
        (N / d : ℕ) + (N / d / 30 : ℕ) := by exact_mod_cast hn
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := d)]
  · rw [ite_eq_right hsmall]
    have hdpos : 0 < d := by omega
    have hdN : d ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    have hqpos : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdN
    have hqsmall : N / d < 6 := by
      apply (Nat.div_lt_iff_lt_mul hdpos).2
      have hNd : N / 6 < d := Nat.lt_of_not_ge hsmall
      have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 6)).1 hNd
      simpa only [Nat.mul_comm] using this
    have hq : N / d = 1 ∨ N / d = 2 ∨ N / d = 3 ∨ N / d = 4 ∨ N / d = 5 := by
      omega
    rcases hq with hq | hq | hq | hq | hq <;> norm_num [hq] <;> linarith

/-- Real-endpoint form of the complementary upper recurrence. -/
theorem chebyshev_psi_le_floor_factorial_combination_add (x : ℝ) :
    Chebyshev.psi x ≤
      Real.log (⌊x⌋₊.factorial : ℝ) - Real.log (⌊x / 2⌋₊.factorial : ℝ) -
        Real.log (⌊x / 3⌋₊.factorial : ℝ) - Real.log (⌊x / 5⌋₊.factorial : ℝ) +
        Real.log (⌊x / 30⌋₊.factorial : ℝ) + Chebyshev.psi (x / 6) := by
  rw [Chebyshev.psi_eq_psi_coe_floor x, Chebyshev.psi_eq_psi_coe_floor (x / 6)]
  simpa only [Nat.floor_div_ofNat] using
    chebyshev_psi_le_factorial_combination_add ⌊x⌋₊

end Problem337

end

end OAI
