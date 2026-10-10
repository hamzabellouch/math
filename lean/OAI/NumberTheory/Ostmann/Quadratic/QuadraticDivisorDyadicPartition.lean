import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDyadicDivisors

namespace OAI

/-! # Disjoint divisor blocks, including the divisor-one boundary -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDivisorDyadicBlock (Q j : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Q).filter (fun d => Nat.log 2 (d - 1) = j)

theorem quadraticDivisorDyadicBlock_subset (Q j : ℕ) :
    quadraticDivisorDyadicBlock Q j ⊆ Finset.Ioc (2 ^ j) (2 * 2 ^ j) := by
  intro d hd
  obtain ⟨hd, hj⟩ := Finset.mem_filter.mp hd
  have hd₂ := (Finset.mem_Icc.mp hd).1
  have hn : d - 1 ≠ 0 := by omega
  have hlo := Nat.pow_log_le_self 2 hn
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (d - 1)
  rw [hj] at hlo hhi
  rw [pow_succ] at hhi
  apply Finset.mem_Ioc.mpr
  omega

theorem quadratic_divisor_dyadic_sum {R : Type*} [AddCommMonoid R] (Q : ℕ) (F : ℕ → R) :
    (∑ j ∈ Finset.range (Nat.log 2 Q + 1),
      ∑ d ∈ quadraticDivisorDyadicBlock Q j, F d) = ∑ d ∈ Finset.Icc 2 Q, F d := by
  simp only [quadraticDivisorDyadicBlock, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : Nat.log 2 (d - 1) < Nat.log 2 Q + 1 := by
    have hh := Nat.log_mono_right (b := 2)
      (show d - 1 ≤ Q by have := (Finset.mem_Icc.mp hd).2; omega)
    omega
  simp only [Finset.sum_ite_eq, Finset.mem_range, hle, ite_true]

theorem quadratic_divisor_sum_one_blocks {R : Type*} [AddCommMonoid R]
    {Q : ℕ} (hQ : 1 ≤ Q) (F : ℕ → R) :
    (∑ d ∈ Finset.Icc 1 Q, F d) = F 1 +
      ∑ j ∈ Finset.range (Nat.log 2 Q + 1), ∑ d ∈ quadraticDivisorDyadicBlock Q j, F d := by
  rw [quadratic_divisor_dyadic_sum]
  have hmem : 1 ∈ Finset.Icc 1 Q := Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩
  have heq : (Finset.Icc 1 Q).erase 1 = Finset.Icc 2 Q := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  rw [← heq, Finset.add_sum_erase _ _ hmem]

theorem quadratic_divisor_sum_blocks_bound {Q : ℕ} (hQ : 1 ≤ Q)
    (F : ℕ → ℂ) (T : ℕ → ℝ)
    (hblocks : ∀ j < Nat.log 2 Q + 1,
      (∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), ‖F d‖) ≤ T j) :
    ‖∑ d ∈ Finset.Icc 1 Q, F d‖ ≤ ‖F 1‖ + ∑ j ∈ Finset.range (Nat.log 2 Q + 1), T j := by
  rw [quadratic_divisor_sum_one_blocks hQ]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  apply (norm_sum_le _ _).trans
  apply le_trans _ (hblocks j (Finset.mem_range.mp hj))
  exact Finset.sum_le_sum_of_subset_of_nonneg (quadraticDivisorDyadicBlock_subset Q j)
    (fun d _ _ => norm_nonneg _)

end Ostmann

end OAI
