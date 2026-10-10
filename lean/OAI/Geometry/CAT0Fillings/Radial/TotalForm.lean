import Mathlib

namespace OAI

section
section
namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def totalRankOneForm (H : Matrix ι ι ℝ) (c : ℝ) (u : ι → ℝ) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℝ :=
  fromBlocks (0 : Matrix Unit Unit ℝ) 0 0 H+
    vecMulVec (Sum.elim (fun _ => c) u) (Sum.elim (fun _ => c) u)

lemma totalRankOneForm_det (H : Matrix ι ι ℝ) (c : ℝ) (u : ι → ℝ) :
    (totalRankOneForm H c u).det = c^2*H.det := by
  let E : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℝ :=
    fromBlocks (Matrix.of fun _ _ => c) 0 (replicateCol Unit u) 1
  let D : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℝ := fromBlocks 1 0 0 H
  have he : totalRankOneForm H c u = E*D*E.transpose := by
    dsimp [E,D]
    rw [Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one,Matrix.one_mul,Matrix.mul_zero,Matrix.zero_mul,
      add_zero,zero_add,Matrix.transpose_zero,Matrix.transpose_one]
    ext i j
    cases i <;> cases j <;>
      simp [totalRankOneForm,Matrix.mul_apply,Matrix.vecMulVec_apply,
        Matrix.replicateCol,Matrix.transpose_apply, mul_comm,add_comm]
  have hd : D.det = H.det := by simp [D,Matrix.det_fromBlocks_zero₂₁]
  have hE : E.det = c := by simp [E,Matrix.det_unique]
  rw [he,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hE,hd]
  ring

lemma det_sub_vecMulVec (G : Matrix ι ι ℝ) (α : ι → ℝ) (hG : G.det ≠ 0) :
    (G-vecMulVec α α).det = G.det*(1-α ⬝ᵥ G⁻¹.mulVec α) := by
  have he : G-vecMulVec α α =
      G+replicateCol Unit (-α)*replicateRow Unit α := by
    ext i j
    simp [Matrix.mul_apply,Matrix.vecMulVec_apply,Matrix.replicateCol,Matrix.replicateRow,
      sub_eq_add_neg]
  rw [he,Matrix.det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hG)]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply,Matrix.one_apply_eq,Matrix.mul_apply,
    Matrix.replicateRow_apply,Matrix.replicateCol_apply,Pi.neg_apply]
  simp only [Finset.sum_neg_distrib,mul_neg]
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [sub_eq_add_neg,mul_assoc]

omit [DecidableEq ι] in

lemma totalRankOneForm_quadratic (H : Matrix ι ι ℝ) (c : ℝ) (u : ι → ℝ)
    (v : Unit ⊕ ι → ℝ) :
    v ⬝ᵥ (totalRankOneForm H c u).mulVec v =
      (c*v (Sum.inl ()) + u ⬝ᵥ (v ∘ Sum.inr))^2 +
        (v ∘ Sum.inr) ⬝ᵥ H.mulVec (v ∘ Sum.inr) := by
  rw [totalRankOneForm,Matrix.add_mulVec,dotProduct_add,Matrix.vecMulVec_mulVec,
    dotProduct_smul,op_smul_eq_smul,smul_eq_mul,dotProduct_comm v]
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec,zero_add,add_zero]
  have hsplit : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := by ext x; cases x <;> rfl
  conv_lhs => rw [hsplit]
  simp only [sumElim_dotProduct_sumElim]
  simp [dotProduct,Function.comp_def,pow_two,mul_comm,add_comm]

omit [DecidableEq ι] in

lemma totalRankOneForm_posSemidef (H : Matrix ι ι ℝ) (c : ℝ) (u : ι → ℝ)
    (hH : H.PosSemidef) : (totalRankOneForm H c u).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.add
    · rw [Matrix.IsHermitian]
      simpa only [Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero]
        using congrArg (fun A => fromBlocks (0 : Matrix Unit Unit ℝ) 0 0 A) hH.isHermitian.eq
    · simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star
        (Sum.elim (fun _ => c) u)).isHermitian
  · intro v
    simp only [star_trivial,totalRankOneForm_quadratic]
    exact add_nonneg (sq_nonneg _) (hH.dotProduct_mulVec_nonneg _)

lemma radial_inverse_norm_le_one (G : Matrix ι ι ℝ) (α : ι → ℝ)
    (hG : G.PosDef) (hα : ∀ v : ι → ℝ, (α ⬝ᵥ v)^2 ≤ v ⬝ᵥ G.mulVec v) :
    α ⬝ᵥ G⁻¹.mulVec α ≤ 1 := by
  have hi : G.mulVec (G⁻¹.mulVec α) = α := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG.det_pos.ne'),
      Matrix.one_mulVec]
  have hh := hα (G⁻¹.mulVec α)
  rw [hi,dotProduct_comm (G⁻¹.mulVec α)] at hh
  by_contra! hn
  have hc := mul_pos (lt_trans zero_lt_one hn) (sub_pos.mpr hn)
  nlinarith

end CAT0Fillings
end
end

end OAI
