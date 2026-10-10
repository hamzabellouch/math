import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealGramDeterminantOrder
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace OAI

/-! # Simultaneous coordinates for two ordered positive quadratic forms -/
noncomputable section
namespace PolycyclicRecognition
open Matrix
open scoped MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem real_posDef_normalizer {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ∃ Q : Matrix ι ι ℝ, IsUnit Q ∧ Qᴴ * A * Q = 1 := by
  obtain ⟨P, hP, hAP⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA.isStrictlyPositive
  let Q := P⁻¹
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  refine ⟨Q, (Matrix.isUnit_iff_isUnit_det Q).mpr
    (Matrix.isUnit_det_of_left_inverse hPQ), ?_⟩
  rw [hAP, ← star_eq_conjTranspose]
  calc
    _ = (star Q * star P) * (P * Q) := by simp only [mul_assoc]
    _ = star (P * Q) := by rw [star_mul, hPQ, mul_one]
    _ = 1 := by rw [hPQ, star_one]

theorem real_ordered_forms_simultaneous_diagonal {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hAB : (B - A).PosSemidef) :
    ∃ (T : Matrix ι ι ℝ) (ev : ι → ℝ), IsUnit T ∧
      Tᴴ * A * T = 1 ∧ Tᴴ * B * T = diagonal ev ∧ ∀ i, 1 ≤ ev i := by
  obtain ⟨Q, hQ, hQA⟩ := real_posDef_normalizer hA
  let C := Qᴴ * B * Q
  have hB : B.PosDef := by simpa using hA.add_posSemidef hAB
  have hC : C.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hB.isHermitian
  have hC1 : (C - 1).PosSemidef := by
    dsimp [C]
    rw [← hQA, ← sub_mul, ← mul_sub]
    exact hAB.conjTranspose_mul_mul_same Q
  let U : Matrix ι ι ℝ := hC.eigenvectorUnitary
  have hU : IsUnit U := Unitary.isUnit_coe
  have hU1 : Uᴴ * U = 1 := by
    change (hC.eigenvectorUnitary : Matrix ι ι ℝ)ᴴ * hC.eigenvectorUnitary = 1
    simpa only [← star_eq_conjTranspose, ← Unitary.coe_star] using
      Unitary.coe_star_mul_self hC.eigenvectorUnitary
  have hdiag : Uᴴ * C * U = diagonal hC.eigenvalues := by
    simpa [U, Unitary.conjStarAlgAut_star_apply, Unitary.coe_star,
      star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      hC.conjStarAlgAut_star_eigenvectorUnitary
  refine ⟨Q * U, hC.eigenvalues, hQ.mul hU, ?_, ?_, fun i =>
    real_matrix_eigenvalues_ge_one hC hC1 i⟩
  · rw [conjTranspose_mul]
    calc
      _ = Uᴴ * (Qᴴ * A * Q) * U := by simp only [mul_assoc]
      _ = 1 := by rw [hQA, Matrix.mul_one, hU1]
  · rw [conjTranspose_mul]
    calc
      _ = Uᴴ * (Qᴴ * B * Q) * U := by simp only [mul_assoc]
      _ = diagonal hC.eigenvalues := hdiag

theorem real_ordered_forms_diagonal_product_bound {A B T : Matrix ι ι ℝ}
    (ev : ι → ℝ) (hTA : Tᴴ * A * T = 1) (hTB : Tᴴ * B * T = diagonal ev)
    (K : ℝ) (hbound : B.det ≤ K ^ Fintype.card ι * A.det) :
    ∏ i, ev i ≤ K ^ Fintype.card ι := by
  have ha : T.det ^ 2 * A.det = 1 := by
    have h := congrArg Matrix.det hTA
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, Matrix.det_one] at h
    calc
      _ = T.det * A.det * T.det := by ring
      _ = 1 := h
  have hb : T.det ^ 2 * B.det = ∏ i, ev i := by
    have h := congrArg Matrix.det hTB
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, Matrix.det_diagonal] at h
    calc
      _ = T.det * B.det * T.det := by ring
      _ = _ := h
  calc
    _ = T.det ^ 2 * B.det := hb.symm
    _ ≤ T.det ^ 2 * (K ^ Fintype.card ι * A.det) :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = K ^ Fintype.card ι := by calc
      _ = K ^ Fintype.card ι * (T.det ^ 2 * A.det) := by ring
      _ = _ := by rw [ha, mul_one]

end PolycyclicRecognition

end

end OAI
