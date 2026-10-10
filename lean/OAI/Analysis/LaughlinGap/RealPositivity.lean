import Mathlib
import OAI.Analysis.LaughlinGap.PhysicalAveraging

namespace OAI

/-! Real Positivity. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma complexify_isPositive_iff (A : Matrix ι ι ℝ) :
    (complexify A).IsPositive ↔ A.PosSemidef := by
  refine ⟨fun h => ?_, complexify_positive⟩
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · have ha : (complexify A).adjoint = complexify A := h.isSymmetric.adjoint_eq
    rw [← complexify_transpose] at ha
    exact (Matrix.isHermitian_iff_isSymm).mpr (complexify_injective ha)
  · have hx := h.re_inner_nonneg_right (WithLp.toLp 2 (fun i => (x i : ℂ)))
    simpa [complexify, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
      Matrix.mulVec, dotProduct, Complex.mul_re, Complex.add_re, mul_comm] using hx

omit [DecidableEq ι] in
lemma transpose_square_positive [DecidableEq ι] (B : Matrix ι ι ℝ) :
    (B.transpose * B).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self B

lemma square_diff_positive {A B : Matrix ι ι ℝ}
    (h : ∀ x, ‖complexify B x‖ ≤ ‖complexify A x‖) :
    (A.transpose * A - B.transpose * B).PosSemidef := by
  rw [← complexify_isPositive_iff, map_sub, map_mul, map_mul,
    complexify_transpose, complexify_transpose]
  apply (LinearMap.isPositive_iff_complex _).mpr
  intro x
  rw [LinearMap.sub_apply]
  simp only [Module.End.mul_apply, inner_sub_left, LinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K]
  change (Complex.ofReal ((Complex.ofReal ‖complexify A x‖ ^ 2 -
      Complex.ofReal ‖complexify B x‖ ^ 2).re) =
      Complex.ofReal ‖complexify A x‖ ^ 2 - Complex.ofReal ‖complexify B x‖ ^ 2 ∧
      (0 : ℝ) ≤ (Complex.ofReal ‖complexify A x‖ ^ 2 - Complex.ofReal ‖complexify B x‖ ^ 2).re)
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.ofReal_re]
  exact ⟨trivial, sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h x))⟩

lemma annihilation_square_le {n : ℕ} (j : Fin n) (B : FockMatrix n) :
    (B.transpose * B - (annihilation j * B).transpose * (annihilation j * B)).PosSemidef := by
  apply square_diff_positive
  intro x
  simpa only [map_mul, complexify_annihilation, Module.End.mul_apply] using
    Occupation.transition_norm_le j false (complexify B x)

lemma double_annihilation_square_le {n : ℕ} (j k : Fin n) (B : FockMatrix n) :
    (B.transpose * B - (annihilation k * (annihilation j * B)).transpose *
      (annihilation k * (annihilation j * B))).PosSemidef := by
  apply square_diff_positive
  intro x
  simpa only [map_mul, complexify_annihilation, Module.End.mul_apply] using
    Occupation.double_annihilation_norm_le j k (complexify B x)

lemma combination_bessel {σ : Type*} [Fintype σ] [DecidableEq σ]
    (S : Matrix σ ι ℝ) (hS : S * S.transpose = 1) (B : ι → Matrix κ κ ℝ) :
    ((∑ i, (B i).transpose * B i) -
      ∑ r, (combination B (S r)).transpose * combination B (S r)).PosSemidef := by
  have h : (1 - S.transpose * S).PosSemidef := by
    have he : 1 - S.transpose * S =
        (1 - S.transpose * S).transpose * (1 - S.transpose * S) := by
      simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
        Matrix.transpose_transpose, sub_mul, mul_sub, one_mul, mul_one]
      rw [Matrix.mul_assoc S.transpose S (S.transpose*S), ← Matrix.mul_assoc S S.transpose S, hS, Matrix.one_mul]
      abel
    rw [he]
    exact transpose_square_positive _
  have he : S.transpose * S = ∑ r, Matrix.vecMulVec (S r) (S r) := by
    ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.sum_apply]
  have hh := lift_positive B h
  rw [map_sub, lift_identity, he, map_sum] at hh
  simpa only [lift_rankOne] using hh

end LaughlinGap.RealOccupation

end

end OAI
