import OAI.Probability.SignedSweeps.WordUpper

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma entropy_monomial_le {I : Type*} [Fintype I] (a : I → ℕ) (ha : ∀ i, 0 < a i)
    {p : ℕ} (hp : 0 < p) (hs : ∑ i, a i = p)
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (hxs : ∑ i, x i ≤ 1) :
    (∏ i, x i ^ a i) ≤ Real.exp (-(∑ i, (a i : ℝ) * Real.log ((p : ℝ) / a i))) := by
  by_cases hzero : ∃ i, x i = 0
  · obtain ⟨i, hi⟩ := hzero
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, zero_pow (ha i).ne'])]
    exact (Real.exp_pos _).le
  have hxp (i : I) : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm (by
    intro h; exact hzero ⟨i, h⟩))
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have ha' (i : I) : (0 : ℝ) < a i := Nat.cast_pos.mpr (ha i)
  have hl (i : I) : (a i : ℝ) * Real.log (x i) +
      (a i : ℝ) * Real.log ((p : ℝ) / a i) ≤ p * x i - a i := by
    have hh := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (mul_pos (hxp i) (div_pos hp' (ha' i)))) (ha' i).le
    rw [Real.log_mul (hxp i).ne' (div_pos hp' (ha' i)).ne'] at hh
    have he : (a i : ℝ) * (x i * ((p : ℝ) / a i) - 1) = p * x i - a i := by
      field_simp [(ha' i).ne']
    simpa only [mul_add, he] using hh
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
  have hs' : ∑ i, (a i : ℝ) = p := by exact_mod_cast hs
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hs'] at hsum
  have hlog : ∑ i, (a i : ℝ) * Real.log (x i) ≤
      -(∑ i, (a i : ℝ) * Real.log ((p : ℝ) / a i)) := by
    nlinarith [mul_le_mul_of_nonneg_left hxs hp'.le]
  calc
    _ = Real.exp (∑ i, (a i : ℝ) * Real.log (x i)) := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      rw [Real.exp_nat_mul, Real.exp_log (hxp i)]
    _ ≤ _ := Real.exp_le_exp.mpr hlog

lemma rowColor_monomial_eq {p : ℕ} {C : Type*} (μ : Partition p)
    (color : Fin (μ.1.colLen 0) ↪ C) (x : C → ℝ) :
    (∏ i, x (rowColorWord μ color i)) = ∏ j, x (color j) ^ μ.1.rowLen j := by
  rw [← Equiv.prod_comp μ.rowEquiv (fun i => x (rowColorWord μ color i)), Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  have he (j : Fin (μ.1.rowLen i)) : rowColorWord μ color (μ.rowEquiv ⟨i,j⟩) = color i := by
    unfold rowColorWord
    congr 1
    apply Fin.ext
    exact μ.rowOf_rowEquiv i j
  simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma rowColor_entropy_monomial_le {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (color : Fin (μ.1.colLen 0) ↪ C)
    (x : C → ℝ) (hx : ∀ i, 0 ≤ x i) (hxs : ∑ i, x i ≤ 1) :
    (∏ i, x (rowColorWord μ color i)) ≤ Real.exp (-partsEntropy p μ.1.rowLens) := by
  by_cases hp : p = 0
  · subst p
    simp [partsEntropy_partition_empty]
  rw [rowColor_monomial_eq, partsEntropy_rowLen]
  apply entropy_monomial_le _ μ.rowLen_pos (Nat.pos_of_ne_zero hp) μ.sum_rowLen _ (fun i => hx _)
  calc
    _ = ∑ i ∈ Finset.univ.map color, x i := (Finset.sum_map ..).symm
    _ ≤ ∑ i, x i := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (by intro i _ _; exact hx i)
    _ ≤ 1 := hxs

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma diagonal_euclidean_norm_bound (t : I → ℝ) (ht : ∀ i, 0 ≤ t i)
    {b : ℝ} (hb : 0 ≤ b) (v : EuclideanSpace ℂ I)
    (hv : ∀ i, b < t i → v i = 0) :
    ‖(Matrix.diagonal (fun i => (t i : ℂ))).toEuclideanLin v‖ ≤ b * ‖v‖ := by
  apply le_of_sq_le_sq _ (mul_nonneg hb (norm_nonneg _))
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he : ((Matrix.diagonal (fun i => (t i : ℂ))).toEuclideanLin v) i = (t i : ℂ) * v i := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht i), mul_pow]
  by_cases hi : b < t i
  · simp [hv i hi]
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (ht i) (le_of_not_gt hi) 2) (sq_nonneg _)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

theorem word_diagonal_density_norm_le {p q : ℕ} (μ : Partition p) (hμ : μ.1.colLen 0 ≤ q)
    (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i) (hxs : ∑ i, x i ≤ 1)
    (v : WordSpace p (Fin q))
    (hv : v ∈ (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p (Fin q))).toSubmodule) :
    ‖(wordMatrixEquiv p (Fin q)).symm
      (wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ)))) v‖ ≤
      Real.exp (-partsEntropy p μ.1.rowLens) * ‖v‖ := by
  let color : Fin (μ.1.colLen 0) ↪ Fin q := ⟨Fin.castLE hμ, Fin.castLE_injective _⟩
  have hweight := rowColor_entropy_monomial_le μ color x hx0 hxs
  have hv' := word_isotypic_weight_support μ hμ x hx hx0 hv
  have hd : wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ))) =
      Matrix.diagonal (fun w : Fin p → Fin q => ∏ i, (x (w i) : ℂ)) := by
    ext w z
    by_cases h : w = z
    · subst z; simp [wordTensorMatrix]
    · rw [Matrix.diagonal_apply_ne _ h]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)
  rw [hd, wordMatrixEquiv_symm]
  simp only [← Complex.ofReal_prod]
  apply diagonal_euclidean_norm_bound (fun w => ∏ i, x (w i))
    (fun w => Finset.prod_nonneg (fun i _ => hx0 _)) (Real.exp_pos _).le v
  intro w hw
  apply hv' w
  exact hweight.trans_lt hw

end SignedSweeps
end

end OAI
