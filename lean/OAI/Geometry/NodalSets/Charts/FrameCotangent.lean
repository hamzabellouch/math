import OAI.Geometry.NodalSets.Charts.InvariantFrameInverse

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def frameLeftInverse (J : Matrix m n ℝ) : Matrix n m ℝ :=
  (J.transpose * J)⁻¹ * J.transpose

lemma frameLeftInverse_mul (J : Matrix m n ℝ) (hJ : Function.Injective J.mulVec) :
    frameLeftInverse J * J = 1 := by
  have hg : (J.transpose * J).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (PosDef.one : (1 : Matrix m m ℝ).PosDef).conjTranspose_mul_mul_same hJ
  exact (Matrix.mul_assoc _ _ _).trans
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne'))

lemma frameLeftInverse_coordinates (J : Matrix m n ℝ) (hJ : Function.Injective J.mulVec)
    (v : n → ℝ) : frameLeftInverse J *ᵥ (J *ᵥ v) = v := by
  rw [mulVec_mulVec,frameLeftInverse_mul J hJ,one_mulVec]

lemma frameLeftInverse_covector (J : Matrix m n ℝ) (hJ : Function.Injective J.mulVec)
    (v : n → ℝ) : J.transpose *ᵥ ((frameLeftInverse J).transpose *ᵥ v) = v := by
  rw [mulVec_mulVec,← transpose_mul,frameLeftInverse_mul J hJ,transpose_one,one_mulVec]

omit [DecidableEq m] in
lemma frameContravariant_pullback (A : Matrix m m ℝ) (J : Matrix m n ℝ) :
    frameContravariant A J = frameLeftInverse J * A * (frameLeftInverse J).transpose := by
  have ht : ((J.transpose * J)⁻¹).transpose = (J.transpose * J)⁻¹ := by
    rw [transpose_nonsing_inv,transpose_mul,transpose_transpose]
  simp only [frameContravariant,frameLeftInverse,transpose_mul,transpose_transpose,ht,Matrix.mul_assoc]

end
end Yau.Geometry

end OAI
