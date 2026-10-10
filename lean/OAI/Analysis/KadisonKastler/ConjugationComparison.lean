import OAI.Analysis.KadisonKastler.CompleteConjugation

namespace OAI

/-! # Complete bounds for two operator conjugations

The smoothing operators need not be unitary. Their conjugation maps still
have a complete comparison bound controlled by their norms and distance.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def operatorConjugationLinear (v : B) : B →ₗ[ℂ] B where
  toFun x := v * x * star v
  map_add' x y := by simp only [mul_add, add_mul]
  map_smul' c x := by simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, RingHom.id_apply]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem operatorConjugationLinear_apply (v x : B) :
    operatorConjugationLinear v x = v * x * star v := rfl

theorem complete_operatorConjugation_sub (v w : B) :
    CompletelyBoundedBy (operatorConjugationLinear v - operatorConjugationLinear w)
      ((‖v‖ + ‖w‖) * ‖v - w‖) := by
  intro p q X
  let P : CStarMatrix (Fin p) (Fin p) B := matrixScalarHom v
  let R : CStarMatrix (Fin p) (Fin p) B := matrixScalarHom w
  let Q : CStarMatrix (Fin q) (Fin q) B := matrixScalarHom (star v)
  let S : CStarMatrix (Fin q) (Fin q) B := matrixScalarHom (star w)
  have hP : ‖P - R‖ ≤ ‖v - w‖ := by
    exact (map_sub (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin p) (Fin p) B) v w) ▸
      NonUnitalStarAlgHom.norm_apply_le
        (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin p) (Fin p) B) (v - w)
  have hQ : ‖Q‖ ≤ ‖v‖ := by
    simpa only [Q, norm_star] using NonUnitalStarAlgHom.norm_apply_le
      (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin q) (Fin q) B) (star v)
  have hR : ‖R‖ ≤ ‖w‖ := NonUnitalStarAlgHom.norm_apply_le
    (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin p) (Fin p) B) w
  have hS : ‖Q - S‖ ≤ ‖v - w‖ := by
    change ‖(matrixScalarHom (star v) : CStarMatrix (Fin q) (Fin q) B) -
      matrixScalarHom (star w)‖ ≤ ‖v - w‖
    rw [← map_sub]
    have h := NonUnitalStarAlgHom.norm_apply_le
      (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin q) (Fin q) B) (star v - star w)
    exact h.trans_eq (by rw [← star_sub, norm_star])
  have hmatrix (a : B) : CStarMatrix.mapₗ (operatorConjugationLinear a) X =
      (matrixScalarHom a : CStarMatrix (Fin p) (Fin p) B) * X *
        (matrixScalarHom (star a) : CStarMatrix (Fin q) (Fin q) B) := by
    apply Matrix.ext
    intro i j
    simp [operatorConjugationLinear, CStarMatrix.mul_apply, matrixScalarHom_apply]
  have hsplit : P * X * Q - R * X * S =
      (P - R) * X * Q + R * X * (Q - S) := by
    have hm (A B' : Matrix (Fin p) (Fin p) B) (Y : Matrix (Fin p) (Fin q) B)
        (C D : Matrix (Fin q) (Fin q) B) :
        A * Y * C - B' * Y * D = (A - B') * Y * C + B' * Y * (C - D) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel
    exact hm P R X Q S
  rw [matrix_map_sub, hmatrix, hmatrix, hsplit]
  calc
    _ ≤ ‖(P - R) * X * Q‖ + ‖R * X * (Q - S)‖ := norm_add_le _ _
    _ ≤ (‖P - R‖ * ‖X‖) * ‖Q‖ + (‖R‖ * ‖X‖) * ‖Q - S‖ :=
      add_le_add
        ((rectangular_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (rectangular_norm_mul_le _ _) (norm_nonneg Q)))
        ((rectangular_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (rectangular_norm_mul_le _ _) (norm_nonneg (Q - S))))
    _ ≤ (‖v - w‖ * ‖X‖) * ‖v‖ + (‖w‖ * ‖X‖) * ‖v - w‖ := by
      gcongr
    _ = ((‖v‖ + ‖w‖) * ‖v - w‖) * ‖X‖ := by ring

end

end KadisonKastler

end OAI
