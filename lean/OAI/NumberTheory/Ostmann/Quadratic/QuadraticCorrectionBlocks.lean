import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorDyadicPartition

namespace OAI

/-! # Exact correction blocks retain the joint frequency sums -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticDivisorDyadicBlock_eq_filter (Q j : ℕ) :
    quadraticDivisorDyadicBlock Q j =
      (Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter (fun d => d ≤ Q) := by
  classical
  ext d
  constructor
  · intro hd
    exact Finset.mem_filter.mpr ⟨quadraticDivisorDyadicBlock_subset Q j hd,
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2⟩
  · intro hd
    obtain ⟨hd, hQ⟩ := Finset.mem_filter.mp hd
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hd
    have hp : 1 ≤ (2 : ℕ) ^ j := one_le_pow₀ (by norm_num)
    have hl : 2 ^ j ≤ d - 1 := by omega
    have hu : d - 1 < 2 ^ (j + 1) := by rw [pow_succ]; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hQ⟩,
      Nat.log_eq_of_pow_le_of_lt_pow hl hu⟩

theorem quadratic_correction_divisor_sum {Q : ℕ} (hQ : 1 ≤ Q) (F : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 Q, F d) = F 1 +
      ∑ j ∈ Finset.range (Nat.log 2 Q + 1),
        ∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0 := by
  rw [quadratic_divisor_sum_one_blocks hQ]
  simp_rw [quadraticDivisorDyadicBlock_eq_filter, Finset.sum_filter]

theorem quadratic_correction_divisor_bound {Q : ℕ} (hQ : 1 ≤ Q)
    (F : ℕ → ℂ) (A : ℝ) (T : ℕ → ℝ) (hunit : ‖F 1‖ ≤ A)
    (hblock : ∀ j < Nat.log 2 Q + 1,
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0‖ ≤ T j) :
    ‖∑ d ∈ Finset.Icc 1 Q, F d‖ ≤ A + ∑ j ∈ Finset.range (Nat.log 2 Q + 1), T j := by
  rw [quadratic_correction_divisor_sum hQ]
  apply (norm_add_le _ _).trans
  exact add_le_add hunit ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j hj => hblock j (Finset.mem_range.mp hj)))

theorem quadraticDyadicDivisors_eq_filter (K j : ℕ) :
    quadraticDyadicDivisors K j = (oddSquarefreeRange (2 * 2 ^ j)).filter
      (fun b => 2 ^ j ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ j) := by
  classical
  ext b
  constructor
  · intro hb
    have hbounds := quadraticDyadicDivisors_bounds hb
    obtain ⟨hb, _⟩ := Finset.mem_filter.mp hb
    obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hb
    rw [pow_succ] at hbounds
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, by omega⟩, ho, hsf⟩,
      hbounds.1, (Finset.mem_Icc.mp hr).2, ?_⟩
    omega
  · intro hb
    obtain ⟨hb, hlo, hK, hhi⟩ := Finset.mem_filter.mp hb
    obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, hK⟩, ho, hsf⟩, ?_⟩
    apply Nat.log_eq_of_pow_le_of_lt_pow hlo
    rw [pow_succ]
    omega

theorem quadratic_correction_frequency_sum (K : ℕ) (F : ℕ → ℂ) :
    (∑ b ∈ oddSquarefreeRange K, F b) =
      ∑ j ∈ Finset.range (Nat.log 2 K + 1), ∑ b ∈ oddSquarefreeRange (2 * 2 ^ j),
        if 2 ^ j ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ j then F b else 0 := by
  rw [← quadratic_dyadic_divisors_sum K F]
  simp_rw [quadraticDyadicDivisors_eq_filter, Finset.sum_filter]

/-- The original rectangular correction sum is bounded by its actual frequency
blocks, with the unit divisor separated before any triangle inequality. -/
theorem quadratic_correction_rectangle_bound {Q : ℕ} (hQ : 1 ≤ Q) (K : ℕ)
    (F : ℕ → ℕ → ℂ) (A : ℕ → ℝ) (T : ℕ → ℕ → ℝ)
    (hunit : ∀ i < Nat.log 2 K + 1,
      ‖∑ b ∈ oddSquarefreeRange (2 * 2 ^ i),
        if 2 ^ i ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ i then F 1 b else 0‖ ≤ A i)
    (hblock : ∀ i < Nat.log 2 K + 1, ∀ j < Nat.log 2 Q + 1,
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), ∑ b ∈ oddSquarefreeRange (2 * 2 ^ i),
        if d ≤ Q ∧ 2 ^ i ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ i then F d b else 0‖ ≤ T i j) :
    ‖∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K, F d b‖ ≤
      ∑ i ∈ Finset.range (Nat.log 2 K + 1),
        (A i + ∑ j ∈ Finset.range (Nat.log 2 Q + 1), T i j) := by
  classical
  conv_lhs =>
    arg 1
    arg 2
    ext d
    rw [quadratic_correction_frequency_sum K (F d)]
  rw [Finset.sum_comm]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply quadratic_correction_divisor_bound hQ _ _ _ (hunit i (Finset.mem_range.mp hi))
  intro j hj
  apply le_trans (le_of_eq ?_) (hblock i (Finset.mem_range.mp hi) j hj)
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d ≤ Q
  · simp only [hd, ite_true, true_and]
  · simp only [hd, ite_false, false_and, Finset.sum_const_zero]

end Ostmann

end OAI
