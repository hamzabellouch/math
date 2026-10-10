import OAI.Geometry.NodalSets.Charts.TangentialMatrixInverse

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def frameContravariant (A : Matrix m m ℝ) (J : Matrix m n ℝ) : Matrix n n ℝ :=
  (J.transpose * J)⁻¹ * (J.transpose * A * J) * (J.transpose * J)⁻¹

lemma invariant_frame_inverse (A : Matrix m m ℝ) (hA : A.PosDef)
    (J : Matrix m n ℝ) (hJ : Function.Injective J.mulVec)
    (T : Matrix n n ℝ) (hT : A * J = J * T)
    {rho : ℝ} (hr : 0 < rho) :
    frameContravariant A J = rho • (J.transpose * weightedBaseMatrix A rho * J)⁻¹ := by
  have hg : (J.transpose * J).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (PosDef.one : (1 : Matrix m m ℝ).PosDef).conjTranspose_mul_mul_same hJ
  have hh : (J.transpose * weightedBaseMatrix A rho * J).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (weightedBaseMatrix_posDef hA hr).conjTranspose_mul_mul_same hJ
  have ht : J.transpose * A = T.transpose * J.transpose := by
    have h := congrArg Matrix.transpose hT
    simpa only [transpose_mul,show A.transpose = A from by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.1.eq] using h
  have hcore : (J.transpose * A * J) * (J.transpose * J)⁻¹ *
      (J.transpose * A⁻¹ * J) = J.transpose * J := by
    calc
      _ = T.transpose * ((J.transpose * J) * (J.transpose * J)⁻¹) *
          (J.transpose * A⁻¹ * J) := by simp only [ht,Matrix.mul_assoc]
      _ = T.transpose * (J.transpose * A⁻¹ * J) := by
        rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne')]; simp
      _ = J.transpose * (A * A⁻¹) * J := by simp only [← Matrix.mul_assoc,← ht]
      _ = J.transpose * J := by
        rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne')]; simp
  have hmul : frameContravariant A J * (J.transpose * weightedBaseMatrix A rho * J) =
      rho • (1 : Matrix n n ℝ) := by
    unfold frameContravariant weightedBaseMatrix
    rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_smul]
    congr 1
    calc
      _ = (J.transpose * J)⁻¹ * ((J.transpose * A * J) * (J.transpose * J)⁻¹ *
          (J.transpose * A⁻¹ * J)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hcore,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne')]
  calc
    frameContravariant A J = frameContravariant A J *
        ((J.transpose * weightedBaseMatrix A rho * J) * (J.transpose * weightedBaseMatrix A rho * J)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hh.det_pos.ne'),mul_one]
    _ = rho • (J.transpose * weightedBaseMatrix A rho * J)⁻¹ := by
      rw [← Matrix.mul_assoc,hmul,Matrix.smul_mul,one_mul]

end
end Yau.Geometry

end OAI
