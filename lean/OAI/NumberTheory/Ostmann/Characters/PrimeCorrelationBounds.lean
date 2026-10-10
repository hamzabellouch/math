import OAI.NumberTheory.Ostmann.Construction.PrimeDiagonalMatching

namespace OAI

/-! # Applying fixed-history pair estimates to the actual permutation sum -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem primePermutationCorrelation_by_histories {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (v : D → ℤ) (c : ((H → P) × D) → ℂ) :
    primePermutationCorrelation P v c =
      ∑ e : Equiv.Perm H, ∑ d : D, ∑ d' : D,
        if v d = v d' then ∑ l, c (l, d) * conj (c (l ∘ e.symm, d')) else 0 := by
  unfold primePermutationCorrelation
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d' _
  split_ifs <;> simp only [Finset.sum_const_zero]

theorem primePermutationCorrelation_norm_bound {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (v : D → ℤ) (c : ((H → P) × D) → ℂ)
    (δ : Equiv.Perm H → ℝ) (hδ : ∀ e, 0 ≤ δ e)
    (hpair : ∀ e d d', v d = v d' →
      ‖∑ l, c (l, d) * conj (c (l ∘ e.symm, d'))‖ ≤ δ e) :
    ‖primePermutationCorrelation P v c‖ ≤ (Fintype.card D : ℝ) ^ 2 * ∑ e, δ e := by
  rw [primePermutationCorrelation_by_histories]
  calc
    _ ≤ ∑ e : Equiv.Perm H, ∑ _d : D, ∑ _d' : D, δ e := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d' _
      split_ifs with he
      · exact hpair e d d' he
      · simpa only [norm_zero] using hδ e
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      ring

end Ostmann

end OAI
