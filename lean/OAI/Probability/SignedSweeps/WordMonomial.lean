import OAI.Probability.SignedSweeps.WordSpectral
import OAI.Probability.SignedSweeps.PairWordTypes

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma word_diagonal_monomial_norm_le {p q : ℕ} (μ : Partition p)
    (hμ : μ.1.colLen 0 ≤ q) (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i)
    (v : WordSpace p (Fin q))
    (hv : v ∈ (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p (Fin q))).toSubmodule) :
    ‖(wordMatrixEquiv p (Fin q)).symm
      (wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ)))) v‖ ≤
      (∏ i, x (Fin.castLE hμ (μ.rowIndex i))) * ‖v‖ := by
  have hv' := word_isotypic_weight_support μ hμ x hx hx0 hv
  have hd : wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ))) =
      Matrix.diagonal (fun w : Fin p → Fin q => ∏ i, (x (w i) : ℂ)) :=
    by
      ext w z
      by_cases h : w = z
      · subst z; simp [wordTensorMatrix]
      · rw [Matrix.diagonal_apply_ne _ h]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)
  rw [hd, wordMatrixEquiv_symm]
  simp only [← Complex.ofReal_prod]
  apply diagonal_euclidean_norm_bound (fun w => ∏ i, x (w i))
    (fun w => Finset.prod_nonneg (fun i _ => hx0 _))
    (Finset.prod_nonneg (fun i _ => hx0 _)) v
  exact hv'

lemma wordTensor_unitary_norm {p : ℕ} {C : Type*} [Fintype C]
    (U : Matrix.unitaryGroup C ℂ) (v : WordSpace p C) :
    ‖(wordMatrixEquiv p C).symm (wordTensorMatrix p U.1) v‖ = ‖v‖ := by
  rw [wordMatrixEquiv_symm]
  exact matrix_unitary_euclidean_norm (wordUnitaryHom p C U) v

theorem word_monomial_norm_le {p q : ℕ} (μ : Partition p)
    (hμ : μ.1.colLen 0 ≤ q) (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i)
    (U : Matrix.unitaryGroup (Fin q) ℂ) (A : Matrix (Fin q) (Fin q) ℂ)
    (hAU : A = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1)
    (v : WordSpace p (Fin q))
    (hv : v ∈ (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p (Fin q))).toSubmodule) :
    ‖((wordMatrixEquiv p (Fin q)).symm (wordTensorMatrix p A)) v‖ ≤
      (∏ i, x (Fin.castLE hμ (μ.rowIndex i))) * ‖v‖ := by
  let W := wordMatrixEquiv p (Fin q)
  let L := W.symm (wordTensorMatrix p U.1)
  let L' := W.symm (wordTensorMatrix p (star U.1))
  have hunit (R : Matrix (Fin q) (Fin q) ℂ) (hR : R ∈ Matrix.unitaryGroup (Fin q) ℂ) :
      wordTensorMatrix p R ∈ Matrix.unitaryGroup (Fin p → Fin q) ℂ := by
    have hI : wordTensorMatrix p (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
      ext w z
      by_cases h : w = z
      · subst z; simp [wordTensorMatrix]
      · rw [Matrix.one_apply_ne h]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)
    rw [Matrix.mem_unitaryGroup_iff] at hR ⊢
    change wordTensorMatrix p R * (wordTensorMatrix p R).conjTranspose = 1
    rw [← wordTensorMatrix_star, ← wordTensorMatrix_mul]
    change wordTensorMatrix p (R * star R) = 1
    rw [hR, hI]
  have hn (z : WordSpace p (Fin q)) : ‖L z‖ = ‖z‖ := by
    have hh := matrix_unitary_euclidean_norm ⟨_, hunit U.1 U.2⟩ z
    rw [show L = _ from wordMatrixEquiv_symm (wordTensorMatrix p U.1)]
    convert hh using 2
    ext i
    rfl
  have hn' (z : WordSpace p (Fin q)) : ‖L' z‖ = ‖z‖ := by
    have hh := matrix_unitary_euclidean_norm ⟨_, hunit (star U.1) (star U).2⟩ z
    rw [show L' = _ from wordMatrixEquiv_symm (wordTensorMatrix p (star U.1))]
    convert hh using 2
    ext i
    rfl
  have hv' := wordTensor_preserves_isotypic μ (star U.1) hv
  have hN := word_diagonal_monomial_norm_le μ hμ x hx hx0 (L' v) hv'
  change ‖W.symm (wordTensorMatrix p A) v‖ ≤ _
  rw [hAU, wordTensorMatrix_mul, wordTensorMatrix_mul, map_mul, map_mul]
  change ‖L (W.symm (wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ)))) (L' v))‖ ≤ _
  simpa only [hn, hn'] using hN

lemma word_projection_monomial_norm_le {p q : ℕ} (μ : Partition p)
    (hμ : μ.1.colLen 0 ≤ q) (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i)
    (U : Matrix.unitaryGroup (Fin q) ℂ) (A : Matrix (Fin q) (Fin q) ℂ)
    (hAU : A = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1)
    (v : WordSpace p (Fin q)) :
    ‖(((wordMatrixEquiv p (Fin q)).symm (wordTensorMatrix p A)) * wordTypeProjection μ (Fin q)) v‖ ≤
      (∏ i, x (Fin.castLE hμ (μ.rowIndex i))) * ‖v‖ := by
  exact (word_monomial_norm_le μ hμ x hx hx0 U A hAU (wordTypeProjection μ (Fin q) v)
    (Submodule.starProjection_apply_mem _ v)).trans
    (mul_le_mul_of_nonneg_left (wordTypeProjection_norm_le μ (Fin q) v)
      (Finset.prod_nonneg (fun i _ => hx0 _)))

lemma pair_rowColor_monomial_le {u v q : ℕ} (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q)
    (x y : Fin q → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxy : (∑ i, x i) + (∑ i, y i) ≤ 1) :
    (∏ i, x (Fin.castLE hα (α.rowIndex i))) *
      (∏ i, y (Fin.castLE hβ (β.rowIndex i))) ≤ Real.exp (-signedEntropy α β) := by
  let e : Fin (α.1.colLen 0) ↪ Fin q := ⟨Fin.castLE hα, Fin.castLE_injective _⟩
  let f : Fin (β.1.colLen 0) ↪ Fin q := ⟨Fin.castLE hβ, Fin.castLE_injective _⟩
  change (∏ i, x (rowColorWord α e i)) * (∏ i, y (rowColorWord β f i)) ≤ _
  by_cases hp : u + v = 0
  · have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    subst u; subst v
    simp [signedEntropy_empty]
  have he : signedEntropy α β =
      ∑ i : Fin (α.1.colLen 0) ⊕ Fin (β.1.colLen 0),
        ((Sum.elim (fun j : Fin (α.1.colLen 0) => α.1.rowLen j)
            (fun j : Fin (β.1.colLen 0) => β.1.rowLen j) i : ℕ) : ℝ) *
          Real.log ((u + v : ℕ) / (Sum.elim (fun j : Fin (α.1.colLen 0) => α.1.rowLen j)
            (fun j : Fin (β.1.colLen 0) => β.1.rowLen j) i)) := by
    simp only [signedEntropy, List.map_append, List.sum_append,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Nat.cast_add]
    exact congrArg₂ (· + ·) (partsEntropy_rowLen α _ ) (partsEntropy_rowLen β _)
  rw [rowColor_monomial_eq, rowColor_monomial_eq, he]
  have hsumX : ∑ i, x (e i) ≤ ∑ i, x i := by
    rw [← Finset.sum_map]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    exact hx i
  have hsumY : ∑ i, y (f i) ≤ ∑ i, y i := by
    rw [← Finset.sum_map]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    exact hy i
  have hb := entropy_monomial_le
    (Sum.elim (fun i : Fin (α.1.colLen 0) => α.1.rowLen i)
      (fun i : Fin (β.1.colLen 0) => β.1.rowLen i))
    (by intro i; cases i with | inl i => exact α.rowLen_pos i | inr i => exact β.rowLen_pos i)
    (Nat.pos_of_ne_zero hp)
    (by simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Partition.sum_rowLen])
    (Sum.elim (fun i => x (e i)) (fun i => y (f i)))
    (by intro i; cases i with | inl i => exact hx _ | inr i => exact hy _)
    (by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      linarith)
  simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] using hb

end SignedSweeps
end

end OAI
