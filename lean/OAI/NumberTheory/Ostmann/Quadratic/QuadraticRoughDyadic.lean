import Mathlib.Algebra.Order.Chebyshev
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoughBound
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDyadicDivisors

namespace OAI

/-! # Disjoint coefficient blocks for the actual rough moment -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDyadicCoeff (N j : ℕ) (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ quadraticDyadicDivisors N j then v n else 0

theorem quadraticDyadicCoeff_below (N j : ℕ) (v : ℕ → ℂ) {n : ℕ}
    (hn : n < 2 ^ j) : quadraticDyadicCoeff N j v n = 0 := by
  apply ite_eq_right
  exact fun h => (not_le_of_gt hn) (quadraticDyadicDivisors_bounds h).1

theorem quadraticDyadicDivisors_subset_double (N j : ℕ) :
    quadraticDyadicDivisors N j ⊆ oddSquarefreeRange (2 * 2 ^ j) := by
  intro n hn
  have hmem := (Finset.mem_filter.mp hn).1
  have hbound := (quadraticDyadicDivisors_bounds hn).2
  rw [pow_succ] at hbound
  obtain ⟨hi, ho, hs⟩ := Finset.mem_filter.mp hmem
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hi).1, by omega⟩, ho, hs⟩

theorem quadraticTransposeSum_dyadic {N j B : ℕ}
    (hB : quadraticDyadicDivisors N j ⊆ oddSquarefreeRange B)
    (v : ℕ → ℂ) (m : ℤ) :
    quadraticTransposeSum B (quadraticDyadicCoeff N j v) m =
      ∑ n ∈ quadraticDyadicDivisors N j, v n * (jacobiSym m n : ℂ) := by
  unfold quadraticTransposeSum quadraticDyadicCoeff
  simp only [ite_mul, zero_mul, ← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hB]

theorem quadraticDyadicCoeff_energy {N j B : ℕ}
    (hB : quadraticDyadicDivisors N j ⊆ oddSquarefreeRange B) (v : ℕ → ℂ) :
    quadraticSieveEnergy B (quadraticDyadicCoeff N j v) =
      ∑ n ∈ quadraticDyadicDivisors N j, ‖v n‖ ^ 2 := by
  unfold quadraticSieveEnergy quadraticDyadicCoeff
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, ← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hB]

theorem quadratic_dyadic_coeff_energy_sum (N : ℕ) (v : ℕ → ℂ) :
    (∑ j ∈ Finset.range (Nat.log 2 N + 1),
      quadraticSieveEnergy (2 * 2 ^ j) (quadraticDyadicCoeff N j v)) =
      quadraticSieveEnergy N v := by
  simp_rw [quadraticDyadicCoeff_energy (quadraticDyadicDivisors_subset_double N _)]
  exact quadratic_dyadic_divisors_sum N (fun n => ‖v n‖ ^ 2)

theorem quadratic_rough_energy_dyadic (M N K : ℕ) (v : ℕ → ℂ) :
    quadraticRoughEnergy M N K v ≤ (Nat.log 2 N + 1 : ℕ) *
      ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        quadraticRoughEnergy M (2 * 2 ^ j) K (quadraticDyadicCoeff N j v) := by
  have hsum (m : ℤ) : quadraticTransposeSum N v m =
      ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        quadraticTransposeSum (2 * 2 ^ j) (quadraticDyadicCoeff N j v) m := by
    simp_rw [quadraticTransposeSum_dyadic (quadraticDyadicDivisors_subset_double N _)]
    exact (quadratic_dyadic_divisors_sum N _).symm
  unfold quadraticRoughEnergy
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro m _
  rw [hsum]
  have hn := norm_sum_le (Finset.range (Nat.log 2 N + 1))
    (fun j => quadraticTransposeSum (2 * 2 ^ j) (quadraticDyadicCoeff N j v) m)
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range (Nat.log 2 N + 1))
    (f := fun j => ‖quadraticTransposeSum (2 * 2 ^ j) (quadraticDyadicCoeff N j v) m‖)
  simp only [Finset.card_range] at hc
  have hp := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc
  have hw := mul_le_mul_of_nonneg_left hp (quadraticSieveBump_nonneg ((m : ℝ) / M))
  simpa only [Finset.mul_sum, mul_left_comm, mul_assoc] using hw

theorem quadraticTransposeSum_trivial (N : ℕ) (v : ℕ → ℂ) (m : ℤ) :
    ‖quadraticTransposeSum N v m‖ ^ 2 ≤ (N : ℝ) * quadraticSieveEnergy N v := by
  have hn := norm_sum_le (oddSquarefreeRange N)
    (fun n => v n * (jacobiSym m n : ℂ))
  have hc := sq_sum_le_card_mul_sum_sq (s := oddSquarefreeRange N)
    (f := fun n => ‖v n * (jacobiSym m n : ℂ)‖)
  have hs : (∑ n ∈ oddSquarefreeRange N, ‖v n * (jacobiSym m n : ℂ)‖ ^ 2) ≤
      quadraticSieveEnergy N v := by
    apply Finset.sum_le_sum
    intro n _
    rcases jacobiSym.trichotomy m n with h | h | h <;> simp [h]
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (hc.trans
    (mul_le_mul (by exact_mod_cast oddSquarefreeRange_card_le N) hs
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)))

theorem quadratic_rough_bound_trivial (M N K : ℕ) :
    QuadraticRoughBound M N K (3 * (M : ℝ) * N) := by
  intro v
  have hcard : (quadraticRoughKernelRange (3 * M) K).card ≤ 3 * M := by
    apply le_trans (Finset.card_filter_le _ _)
    apply le_trans (Finset.card_filter_le _ _)
    simp
  calc
    _ ≤ ∑ _m ∈ quadraticRoughKernelRange (3 * M) K,
        (N : ℝ) * quadraticSieveEnergy N v := by
      apply Finset.sum_le_sum
      intro m _
      exact (mul_le_mul (quadraticSieveBump_le_one _) (quadraticTransposeSum_trivial N v m)
        (sq_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = (quadraticRoughKernelRange (3 * M) K).card *
        ((N : ℝ) * quadraticSieveEnergy N v) := by simp
    _ ≤ (3 * (M : ℝ)) * ((N : ℝ) * quadraticSieveEnergy N v) := by
      apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      exact_mod_cast hcard
    _ = _ := by ring

end Ostmann

end OAI
