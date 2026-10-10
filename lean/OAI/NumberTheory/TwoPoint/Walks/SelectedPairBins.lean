import OAI.NumberTheory.TwoPoint.Bounds.ComplexPairSelection

namespace OAI

/-! Reindexing a selected numerical pair family into the literal graph bins. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma selected_pair_bin_sum {M : Type*} [AddCommMonoid M]
    (D R : Finset ℕ) (A : Finset (ℕ × ℕ)) (hA : A ⊆ D ×ˢ R)
    (bins : Finset ℤ) (b : ℕ × ℕ → ℤ) (hb : ∀ dq ∈ A, b dq ∈ bins)
    (F : ℤ → ℕ → ℕ → M) :
    (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R,
      if (d, q) ∈ A ∧ b (d, q) = j then F j d q else 0) =
        ∑ dq ∈ A, F (b dq) dq.1 dq.2 := by
  rw [sum_comm]
  have he (d : ℕ) (q : ℕ) :
      (∑ j ∈ bins, if (d, q) ∈ A ∧ b (d, q) = j then F j d q else 0) =
        if (d, q) ∈ A then F (b (d, q)) d q else 0 := by
    by_cases hmem : (d, q) ∈ A
    · simp only [hmem, true_and]
      rw [sum_eq_single (b (d, q))]
      · simp
      · intro j _ hj
        rw [ite_eq_right (Ne.symm hj)]
      · intro hn
        exact (hn (hb _ hmem)).elim
    · simp only [hmem, false_and, ite_false, sum_const_zero]
  calc
    _ = ∑ d ∈ D, ∑ q ∈ R, if (d, q) ∈ A then F (b (d, q)) d q else 0 := by
      apply sum_congr rfl
      intro d _
      rw [sum_comm]
      apply sum_congr rfl
      intro q _
      exact he d q
    _ = ∑ dq ∈ D ×ˢ R, if dq ∈ A then F (b dq) dq.1 dq.2 else 0 := by
      rw [sum_product]
    _ = _ := by
      rw [← sum_filter]
      congr 1
      ext dq
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩

lemma selected_fullComplexBin_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (hR : ∀ q ∈ R, 0 < q)
    (A : Finset (ℕ × ℕ)) (hA : A ⊆ primeTupleDivisors P ×ˢ R)
    (bins : Finset ℤ) (b : ℕ × ℕ → ℤ) (hb : ∀ dq ∈ A, b dq ∈ bins)
    (F G : ℕ → ℂ) (h : ℕ) (T : ℤ → ℝ) :
    (∑ j ∈ bins, fullComplexBin P R
      (fun d q => (d, q) ∈ A ∧ b (d, q) = j) F G h (T j)) =
      ∑ dq ∈ A, (actualPaddingCoefficient dq.2 : ℂ) *
        (positivePrefix (fun n => F ((dq.2 * dq.1) * n) *
          G ((dq.2 * dq.1) * (n + h)))
            (⌊T (b dq)⌋₊ / (dq.2 * dq.1)) / (T (b dq) : ℂ)) := by
  calc
    _ = ∑ j ∈ bins, ∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        if (d, q) ∈ A ∧ b (d, q) = j then
          (actualPaddingCoefficient q : ℂ) *
            (positivePrefix (fun n => F ((q * d) * n) * G ((q * d) * (n + h)))
              (⌊T j⌋₊ / (q * d)) / (T j : ℂ)) else 0 := by
      apply sum_congr rfl
      intro j _
      rw [fullComplexBin_eq_dilated P hprime hdisjoint R
        hR, sum_comm]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro q _
      by_cases hc : (d, q) ∈ A ∧ b (d, q) = j <;> simp [hc]
    _ = _ := selected_pair_bin_sum (primeTupleDivisors P) R
      A hA bins b hb _

end TwoPointCorrelations

end OAI
