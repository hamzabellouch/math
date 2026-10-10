import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstMomentTransform

namespace OAI

/-! # The actual diagonal contribution to the rough quadratic moment -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticRoughDiagonal (M N K : ℕ) (v : ℕ → ℂ) : ℝ :=
  ∑ n ∈ oddSquarefreeRange N, ‖v n‖ ^ 2 *
    ∑ m ∈ quadraticRoughKernelRange (3 * M) K,
      quadraticSieveBump ((m : ℝ) / M) * (jacobiSym m n : ℝ) ^ 2

noncomputable def quadraticRoughOffDiagonal (M N K : ℕ) (v : ℕ → ℂ) : ℂ :=
  ∑ z ∈ ((oddSquarefreeRange N).product (oddSquarefreeRange N)).filter (fun z => z.1 ≠ z.2),
    v z.1 * conj (v z.2) * ∑ m ∈ quadraticRoughKernelRange (3 * M) K,
      quadraticSieveWeight ((m : ℝ) / M) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ)

theorem quadratic_rough_diagonal_bound (M N K : ℕ) (v : ℕ → ℂ) :
    quadraticRoughDiagonal M N K v ≤ (3 * M : ℝ) * quadraticSieveEnergy N v := by
  have hcard : (quadraticRoughKernelRange (3 * M) K).card ≤ 3 * M := by
    apply le_trans (Finset.card_filter_le _ _)
    apply le_trans (Finset.card_filter_le _ _)
    simp
  have hsum (n : ℕ) : (∑ m ∈ quadraticRoughKernelRange (3 * M) K,
      quadraticSieveBump ((m : ℝ) / M) * (jacobiSym m n : ℝ) ^ 2) ≤ (3 * M : ℝ) := by
    calc
      _ ≤ ∑ _m ∈ quadraticRoughKernelRange (3 * M) K, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m _
        have hJ : (jacobiSym m n : ℝ) ^ 2 ≤ 1 := by
          rcases jacobiSym.trichotomy (m : ℤ) n with h | h | h <;> rw [h] <;> norm_num
        exact (mul_le_mul (quadraticSieveBump_le_one _) hJ (sq_nonneg _) zero_le_one).trans_eq (one_mul 1)
      _ = ((quadraticRoughKernelRange (3 * M) K).card : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast hcard
  unfold quadraticRoughDiagonal quadraticSieveEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have hh := mul_le_mul_of_nonneg_left (hsum n) (sq_nonneg ‖v n‖)
  simpa only [mul_comm] using hh

theorem quadratic_rough_diagonal_decomposition (M N K : ℕ) (v : ℕ → ℂ) :
    (quadraticRoughEnergy M N K v : ℂ) =
      (quadraticRoughDiagonal M N K v : ℂ) + quadraticRoughOffDiagonal M N K v := by
  let S := oddSquarefreeRange N
  let F : ℕ × ℕ → ℂ := fun z => v z.1 * conj (v z.2) *
    ∑ m ∈ quadraticRoughKernelRange (3 * M) K,
      quadraticSieveWeight ((m : ℝ) / M) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ)
  have he : (quadraticRoughEnergy M N K v : ℂ) = ∑ z ∈ S.product S, F z := by
    unfold quadraticRoughEnergy
    push_cast
    simp_rw [quadraticTranspose_norm_sq_expand, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    dsimp [F]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [quadraticSieveWeight_apply]
    ring
  have hd : (∑ z ∈ (S.product S).filter (fun z => z.1 = z.2), F z) =
      (quadraticRoughDiagonal M N K v : ℂ) := by
    have hs : (∑ z ∈ (S.product S).filter (fun z => z.1 = z.2), F z) = ∑ n ∈ S, F (n, n) := by
      rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.sum_ite_eq, hn, ite_true]
    rw [hs]
    unfold quadraticRoughDiagonal
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    dsimp [F]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [quadraticSieveWeight_apply, ← Complex.mul_conj']
    ring
  rw [he, ← hd]
  exact (Finset.sum_filter_add_sum_filter_not (S.product S) (fun z => z.1 = z.2) F).symm

theorem quadratic_rough_energy_off_diagonal (M N K : ℕ) (v : ℕ → ℂ) :
    quadraticRoughEnergy M N K v ≤
      (3 * M : ℝ) * quadraticSieveEnergy N v + ‖quadraticRoughOffDiagonal M N K v‖ := by
  have he := congrArg Complex.re (quadratic_rough_diagonal_decomposition M N K v)
  simp only [Complex.ofReal_re, Complex.add_re] at he
  rw [he]
  exact add_le_add (quadratic_rough_diagonal_bound M N K v) (Complex.re_le_norm _)

end Ostmann

end OAI
