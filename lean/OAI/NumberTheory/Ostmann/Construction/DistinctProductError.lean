import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.NumberTheory.Ostmann.Construction.DistinctTupleProducts
import OAI.NumberTheory.Ostmann.Preliminaries.FallingFactorialError

namespace OAI

/-! # A concrete error bound for deleting repeated indices -/

namespace Ostmann

open scoped BigOperators Classical

theorem distinct_product_error {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (y : A → ℂ) (hy : ∀ a, ‖y a‖ ≤ 1) :
    ‖(∑ a, y a) ^ k - ∑ e : Fin k ↪ A, ∏ i, y (e i)‖ ≤
      ((Fintype.card A) ^ k - (Fintype.card A).descFactorial k : ℕ) := by
  let F : (Fin k → A) → ℂ := fun f => ∏ i, y (f i)
  have he : (∑ f : {f : Fin k → A // Function.Injective f}, F f) =
      ∑ e : Fin k ↪ A, ∏ i, y (e i) := by
    exact (Equiv.subtypeInjectiveEquivEmbedding (Fin k) A).sum_comp (fun e => ∏ i, y (e i))
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun f : Fin k → A => Function.Injective f) F
  rw [he] at hsplit
  have hdiff : (∑ a, y a) ^ k - ∑ e : Fin k ↪ A, ∏ i, y (e i) =
      ∑ f : {f : Fin k → A // ¬Function.Injective f}, F f := by
    rw [Fintype.sum_pow]
    change (∑ f, F f) - _ = _
    rw [← hsplit, add_sub_cancel_left]
  rw [hdiff]
  calc
    _ ≤ ∑ f : {f : Fin k → A // ¬Function.Injective f}, ‖F f‖ := norm_sum_le _ _
    _ ≤ ∑ _f : {f : Fin k → A // ¬Function.Injective f}, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro f _
      dsimp only [F]
      rw [Complex.norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hy (f.1 i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      congr 1
      rw [Fintype.card_subtype_compl]
      have hc := Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) A)
      rw [hc, Fintype.card_embedding_eq]
      simp

/-- For a nonempty finite population, the normalized deletion error is at
most k²/J. This suffices for kernels whose bias is bounded below. -/
theorem normalized_distinct_product_error {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (hk : 1 ≤ k) (y : A → ℂ) (hy : ∀ a, ‖y a‖ ≤ 1)
    (hA : 0 < Fintype.card A) :
    ‖((∑ a, y a) / (Fintype.card A : ℂ)) ^ k -
      (∑ e : Fin k ↪ A, ∏ i, y (e i)) / (Fintype.card A : ℂ) ^ k‖ ≤
        (k : ℝ) ^ 2 / Fintype.card A := by
  let J := Fintype.card A
  have hJ : (0 : ℝ) < J := by exact_mod_cast hA
  have hpow : (0 : ℝ) < (J : ℝ) ^ k := pow_pos hJ k
  have hraw := distinct_product_error k y hy
  have hcount := pow_le_descFactorial_add J hA k
  have hcountR : ((J ^ k - J.descFactorial k : ℕ) : ℝ) ≤
      (k : ℝ) ^ 2 * (J : ℝ) ^ (k - 1) := by
    exact_mod_cast (show J ^ k - J.descFactorial k ≤ k ^ 2 * J ^ (k - 1) by omega)
  have hpoweq : (J : ℝ) ^ k = (J : ℝ) * (J : ℝ) ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [div_pow, ← sub_div, norm_div]
  have hnorm : ‖(Fintype.card A : ℂ) ^ k‖ = (J : ℝ) ^ k := by
    rw [norm_pow]
    simp [J]
  rw [hnorm]
  calc
    _ ≤ ((k : ℝ) ^ 2 * (J : ℝ) ^ (k - 1)) / (J : ℝ) ^ k :=
      div_le_div_of_nonneg_right (hraw.trans hcountR) hpow.le
    _ = _ := by
      rw [hpoweq]
      field_simp
      rfl

end Ostmann

end OAI
