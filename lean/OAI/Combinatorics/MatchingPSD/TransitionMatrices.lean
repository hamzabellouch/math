import OAI.Combinatorics.MatchingPSD.ColoringCounts

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix

variable {V : Type u_1} {C : Type u_2} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

noncomputable def tensorKernel (U : Matrix C C ℝ) : Matrix (V → C) (V → C) ℝ :=
  fun f g => ∏ v, U (f v) (g v)

omit [DecidableEq C] in
lemma tensorKernel_mul (U W : Matrix C C ℝ) :
    tensorKernel (V := V) (U * W) = tensorKernel (V := V) U * tensorKernel W := by
  classical
  ext f g
  simp only [tensorKernel, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro h _
  exact Finset.prod_mul_distrib

omit [Fintype C] [DecidableEq V] [DecidableEq C] in
lemma tensorKernel_transpose (U : Matrix C C ℝ) :
    tensorKernel (V := V) U.transpose = (tensorKernel U).transpose := rfl

omit [Fintype C] [DecidableEq V] in
lemma tensorKernel_one :
    tensorKernel (V := V) (1 : Matrix C C ℝ) = 1 := by
  classical
  ext f g
  by_cases h : f = g
  · subst g; simp [tensorKernel]
  · have he : ∃ v, f v ≠ g v := Function.ne_iff.mp h
    obtain ⟨v, hv⟩ := he
    simp only [tensorKernel, Matrix.one_apply, ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [hv]

lemma tensorKernel_orthogonal (U : Matrix C C ℝ)
    (hU : U.transpose * U = 1) :
    (tensorKernel (V := V) U).transpose * tensorKernel (V := V) U = 1 := by
  rw [← tensorKernel_transpose, ← tensorKernel_mul, hU, tensorKernel_one]

lemma tensorKernel_overlap (U : Matrix C C ℝ)
    (hU : U.transpose * U = 1) (x y : (V → C) → ℝ) :
    (tensorKernel U *ᵥ x) ⬝ᵥ (tensorKernel U *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, tensorKernel_orthogonal U hU,
    Matrix.vecMul_one]

omit [Fintype C] [DecidableEq V] [DecidableEq C] in
lemma tensorKernel_relabel (U : Matrix C C ℝ) (σ : Equiv.Perm V) (f g : V → C) :
    tensorKernel U (f ∘ σ) (g ∘ σ) = tensorKernel U f g := by
  exact Equiv.prod_comp σ (fun v => U (f v) (g v))

omit [DecidableEq C] in
lemma tensorKernel_mulVec_relabel (U : Matrix C C ℝ) (σ : Equiv.Perm V)
    (x : (V → C) → ℝ) (f : V → C) :
    (tensorKernel U *ᵥ (fun g => x (g ∘ σ))) f =
      (tensorKernel U *ᵥ x) (f ∘ σ) := by
  classical
  let e : (V → C) ≃ (V → C) := Equiv.arrowCongr σ (Equiv.refl C)
  change ∑ g, tensorKernel U f g * x (g ∘ σ) =
    ∑ g, tensorKernel U (f ∘ σ) g * x g
  refine Fintype.sum_equiv e.symm _ _ ?_
  intro g
  have he : e.symm g = g ∘ σ := rfl
  rw [he, tensorKernel_relabel]

variable {H : Type u_3} [Fintype H] [DecidableEq H]

noncomputable def pairDiagonal (d : C → ℝ) (f : H × Bool → C) : ℝ :=
  if pairConstant f then ∏ i, d (f (i, false)) else 0

noncomputable def pairWeight (A : Matrix C C ℝ) (f : H × Bool → C) : ℝ :=
  ∏ i, A (f (i, false)) (f (i, true))

lemma tensorKernel_mulVec_pairDiagonal (U : Matrix C C ℝ) (d : C → ℝ)
    (f : H × Bool → C) :
    (tensorKernel U *ᵥ pairDiagonal d) f =
      pairWeight (U * diagonal d * U.transpose) f := by
  classical
  change ∑ g, (∏ v, U (f v) (g v)) *
    (if pairConstant g then ∏ i, d (g (i, false)) else 0) = _
  simp only [mul_ite, mul_zero]
  rw [sum_pairConstant]
  simp only [duplicateColoring, Fintype.prod_prod_type, Fintype.prod_bool]
  have hm (a b : C) : (U * diagonal d * U.transpose) a b =
      ∑ c, U a c * d c * U b c := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [pairWeight, hm]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

lemma pairWeight_overlap (U : Matrix C C ℝ) (d : C → ℝ)
    (hU : U.transpose * U = 1) (σ : Equiv.Perm (H × Bool)) :
    (∑ f : H × Bool → C, pairWeight (U * diagonal d * U.transpose) f *
      pairWeight (U * diagonal d * U.transpose) (f ∘ σ)) =
    ∑ f : H × Bool → C, pairDiagonal d f * pairDiagonal d (f ∘ σ) := by
  simp_rw [← tensorKernel_mulVec_pairDiagonal,
    ← tensorKernel_mulVec_relabel U σ (pairDiagonal d)]
  exact tensorKernel_overlap U hU _ _

omit [Fintype C] [DecidableEq H] in
lemma pairDiagonal_abs_le (d : C → ℝ) (hd : ∀ c, |d c| ≤ 1) (f : H × Bool → C) :
    |pairDiagonal d f| ≤ 1 := by
  classical
  unfold pairDiagonal
  split_ifs
  · rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => hd _)
  · simp

lemma pairWeight_overlap_le (U : Matrix C C ℝ) (d : C → ℝ)
    (hU : U.transpose * U = 1) (hd : ∀ c, |d c| ≤ 1)
    (σ : Equiv.Perm (H × Bool)) :
    (∑ f : H × Bool → C, pairWeight (U * diagonal d * U.transpose) f *
      pairWeight (U * diagonal d * U.transpose) (f ∘ σ)) ≤
    (Fintype.card {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ) := by
  classical
  rw [pairWeight_overlap U d hU σ]
  have he : (Fintype.card {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ) =
      ∑ f : H × Bool → C, if pairConstant f ∧ pairConstant (f ∘ σ) then (1 : ℝ) else 0 := by
    simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro f _
    split_ifs <;> norm_num
  rw [he]
  apply Finset.sum_le_sum
  intro f _
  by_cases hf : pairConstant f ∧ pairConstant (f ∘ σ)
  · rw [ite_eq_left hf]
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact (mul_le_mul (pairDiagonal_abs_le d hd f)
        (pairDiagonal_abs_le d hd (f ∘ σ)) (abs_nonneg _) zero_le_one).trans_eq (mul_one _))
  · rw [ite_eq_right hf]
    rcases not_and_or.mp hf with hf | hf <;> simp [pairDiagonal, hf]

end MatchingSmoothing

end OAI
