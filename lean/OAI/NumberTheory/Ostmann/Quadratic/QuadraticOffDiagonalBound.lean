import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOffDiagonalPairSums

namespace OAI

/-! # Removing the diagonal preserves a uniform quadratic-form bound -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticDiagonalKernel (N : ℕ) (v : ℕ → ℂ)
    (E : ℕ → ℕ × ℕ → ℂ) : ℂ :=
  ∑ n ∈ oddSquarefreeRange N, (‖v n‖ ^ 2 : ℂ) * E n (n, n)

theorem quadratic_gcd_kernel_pairs (N : ℕ) (v : ℕ → ℂ) (E : ℕ → ℕ × ℕ → ℂ) :
    quadraticGcdRemainder N v E =
      ∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
        v z.1 * conj (v z.2) * E (z.1.gcd z.2) z := by
  rw [quadratic_pair_sum_gcd]
  unfold quadraticGcdRemainder
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro z hz
  rw [(Finset.mem_filter.mp hz).2]

theorem quadratic_gcd_kernel_diagonal (N : ℕ) (v : ℕ → ℂ) (E : ℕ → ℕ × ℕ → ℂ) :
    quadraticGcdRemainder N v E = quadraticDiagonalKernel N v E +
      quadraticGcdRemainder N v (fun D z => if z.1 = z.2 then 0 else E D z) := by
  rw [quadratic_gcd_kernel_pairs, quadratic_gcd_off_diagonal]
  have hd : (∑ z ∈ ((oddSquarefreeRange N).product (oddSquarefreeRange N)).filter
      (fun z => z.1 = z.2), v z.1 * conj (v z.2) * E (z.1.gcd z.2) z) =
      quadraticDiagonalKernel N v E := by
    rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
    unfold quadraticDiagonalKernel
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.sum_ite_eq, hn, ite_true, Nat.gcd_self, ← Complex.mul_conj']
  rw [← hd]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem quadratic_gcd_kernel_unit {N n : ℕ} (hn : n ∈ oddSquarefreeRange N)
    (E : ℕ → ℕ × ℕ → ℂ) :
    quadraticGcdRemainder N (fun m => if m = n then 1 else 0) E = E n (n, n) := by
  rw [quadratic_gcd_kernel_pairs, Finset.product_eq_sprod, Finset.sum_product]
  simp [hn]

theorem quadratic_energy_unit {N n : ℕ} (hn : n ∈ oddSquarefreeRange N) :
    quadraticSieveEnergy N (fun m => if m = n then 1 else 0) = 1 := by
  unfold quadraticSieveEnergy
  rw [Finset.sum_eq_single_of_mem n hn]
  · simp
  · intro m _ hm
    simp [hm]

theorem quadratic_off_diagonal_of_bound (N : ℕ) (E : ℕ → ℕ × ℕ → ℂ)
    {T : ℝ}
    (h : ∀ v : ℕ → ℂ, ‖quadraticGcdRemainder N v E‖ ≤ T * quadraticSieveEnergy N v)
    (v : ℕ → ℂ) :
    ‖quadraticGcdRemainder N v (fun D z => if z.1 = z.2 then 0 else E D z)‖ ≤
      2 * T * quadraticSieveEnergy N v := by
  have hp (n : ℕ) (hn : n ∈ oddSquarefreeRange N) : ‖E n (n, n)‖ ≤ T := by
    have hh := h (fun m => if m = n then 1 else 0)
    rwa [quadratic_gcd_kernel_unit hn, quadratic_energy_unit hn, mul_one] at hh
  have hd : ‖quadraticDiagonalKernel N v E‖ ≤ T * quadraticSieveEnergy N v := by
    unfold quadraticDiagonalKernel
    calc
      _ ≤ ∑ n ∈ oddSquarefreeRange N, ‖(‖v n‖ ^ 2 : ℂ) * E n (n, n)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ oddSquarefreeRange N, ‖v n‖ ^ 2 * T := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hp n hn) (sq_nonneg _)
      _ = _ := by
        simp only [quadraticSieveEnergy, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
  have he := quadratic_gcd_kernel_diagonal N v E
  have he' : quadraticGcdRemainder N v (fun D z => if z.1 = z.2 then 0 else E D z) =
      quadraticGcdRemainder N v E - quadraticDiagonalKernel N v E := by rw [he]; ring
  rw [he']
  exact (norm_sub_le _ _).trans ((add_le_add (h v) hd).trans_eq (by ring))

end Ostmann

end OAI
