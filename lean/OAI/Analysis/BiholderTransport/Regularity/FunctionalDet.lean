import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.DeterminantOrder

namespace OAI

section

noncomputable section
open Matrix
open scoped MatrixOrder

namespace WeakMTWTransport
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma determinant_gain_of_functional_bounds [Nonempty n]
    {L V W : Matrix n n ℝ} {e p pi : n → ℝ} {m beta gamma : ℝ}
    (hL : L.IsHermitian) (he : L *ᵥ e = 0)
    (hq : 0 < p ⬝ᵥ e) (hqi : p ⬝ᵥ e ≤ pi ⬝ᵥ e)
    (hm : 0 < m) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hV : V.PosDef) (hVL : V ≤ L + beta • Matrix.vecMulVec p p)
    (hLW : m • L + gamma • Matrix.vecMulVec pi pi ≤ W) :
    gamma * m ^ (Fintype.card n - 1) * V.det ≤ beta * W.det := by
  let q := p ⬝ᵥ e
  let qi := pi ⬝ᵥ e
  let t := Real.sqrt (gamma / (m * beta))
  have hq0 : q ≠ 0 := ne_of_gt hq
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos hgamma (mul_pos hm hbeta))
  have ht2 : t ^ 2 = gamma / (m * beta) :=
    Real.sq_sqrt (le_of_lt (div_pos hgamma (mul_pos hm hbeta)))
  let a : n → ℝ := q⁻¹ • (t • pi - p)
  let S : Matrix n n ℝ := 1 + Matrix.vecMulVec e a
  have hSp : Sᵀ *ᵥ p = t • pi := by
    dsimp [S]
    rw [Matrix.mulVec_transpose, Matrix.vecMul_add, Matrix.vecMul_one,
      Matrix.vecMul_vecMulVec]
    change p + q • (q⁻¹ • (t • pi - p)) = t • pi
    rw [smul_smul, mul_inv_cancel₀ hq0, one_smul, add_sub_cancel]
  have hSdet : S.det = t * qi / q := by
    dsimp [S]
    rw [det_one_add_vecMulVec]
    dsimp [a]
    rw [smul_dotProduct, sub_dotProduct, smul_dotProduct]
    change 1 + q⁻¹ * (t * qi - q) = t * qi / q
    field_simp
    ring
  have hSge : t ≤ S.det := by
    rw [hSdet, le_div_iff₀ hq]
    exact mul_le_mul_of_nonneg_left hqi ht.le
  have hSpos : 0 < S.det := ht.trans_le hSge
  have hSinj : Function.Injective S.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det S).2 (isUnit_iff_ne_zero.2 hSpos.ne'))
  have hsmall : (m • (Sᵀ * V * S)).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hV.conjTranspose_mul_mul_same hSinj).smul hm
  have hfix : Sᵀ * L * S = L := oblique_fixes_kernel_form hL he a
  have hscalar : m * beta * t ^ 2 = gamma := by
    rw [ht2]
    field_simp
  have heq : m • (Sᵀ * (L + beta • Matrix.vecMulVec p p) * S) =
      m • L + gamma • Matrix.vecMulVec pi pi := by
    rw [Matrix.mul_add Sᵀ L (beta • Matrix.vecMulVec p p), Matrix.add_mul, hfix, smul_add,
      Matrix.mul_smul, Matrix.smul_mul, congruence_rank_one, hSp]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, Pi.smul_apply]
    linear_combination pi i * pi j * hscalar
  have horder : m • (Sᵀ * V * S) ≤ W := by
    apply le_trans _ hLW
    rw [← heq]
    have h := (transpose_congruence_mono hVL S).smul hm.le
    rw [Matrix.le_iff]
    simpa only [smul_sub] using h
  have hdet := det_le_of_posDef_le hsmall horder
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hsquare : t ^ 2 ≤ S.det ^ 2 := by nlinarith
  have hmpow : 0 < m ^ Fintype.card n := pow_pos hm _
  have hlower : m ^ Fintype.card n * t ^ 2 * V.det ≤ W.det := by
    nlinarith [mul_nonneg (mul_nonneg hmpow.le (sub_nonneg.2 hsquare)) hV.det_pos.le]
  have hcard : Fintype.card n = (Fintype.card n - 1) + 1 :=
    (Nat.sub_add_cancel Fintype.card_pos).symm
  have hpower : m ^ Fintype.card n = m ^ (Fintype.card n - 1) * m := by
    conv_lhs => rw [hcard, pow_succ]
  have hcancel : beta * (m ^ Fintype.card n * t ^ 2 * V.det) =
      gamma * m ^ (Fintype.card n - 1) * V.det := by
    rw [hpower]
    calc
      beta * (m ^ (Fintype.card n - 1) * m * t ^ 2 * V.det) =
          m ^ (Fintype.card n - 1) * V.det * (m * beta * t ^ 2) := by ring
      _ = gamma * m ^ (Fintype.card n - 1) * V.det := by rw [hscalar]; ring
  rw [← hcancel]
  exact mul_le_mul_of_nonneg_left hlower hbeta.le

end WeakMTWTransport

end
end

end OAI
