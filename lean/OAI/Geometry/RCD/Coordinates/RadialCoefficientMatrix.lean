import OAI.Geometry.RCD.Coordinates.MatrixNormConversion

namespace OAI

/-! # Stacking the scalar radial fits in the same normalizing frame -/

open scoped BigOperators InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

def radialCoefficientMatrix {n : ℕ} (N : Euclidean n ≃L[ℝ] Euclidean n)
    (coeff : Fin n → Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (N.symm (coeff i)) j

/-- The stacked coefficient matrix acts on normalized coordinate values
by the original scalar affine coefficients. -/
theorem radialCoefficientMatrix_action {n : ℕ}
    (N : Euclidean n ≃L[ℝ] Euclidean n) (coeff : Fin n → Euclidean n)
    (x : Euclidean n) (i : Fin n) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (radialCoefficientMatrix N coeff)
      ((N : Euclidean n →L[ℝ] Euclidean n).adjoint x) i = ⟪x, coeff i⟫_ℝ := by
  have hi := ContinuousLinearMap.adjoint_inner_left (N : Euclidean n →L[ℝ] Euclidean n)
    (N.symm (coeff i)) x
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hi
  rw [real_inner_comm] at hi
  convert hi using 1
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    radialCoefficientMatrix, PiLp.inner_apply, Real.inner_apply]

/-- The scalar coefficient errors give a near-identity matrix in the
operator norm, with only the fixed dimension loss. -/
theorem radialCoefficientMatrix_sub_id_norm {n : ℕ}
    (N : Euclidean n ≃L[ℝ] Euclidean n) (coeff : Fin n → Euclidean n)
    {η : ℝ} (hη : 0 ≤ η)
    (hcoeff : ∀ i, ‖N.symm (coeff i - N (EuclideanSpace.single i 1))‖ ≤ η) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (radialCoefficientMatrix N coeff) -
      ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤ (n : ℝ) ^ 2 * η := by
  apply matrix_sub_id_norm_le_of_entries _ hη
  intro i j
  have hpoint := (PiLp.norm_apply_le (N.symm (coeff i - N (EuclideanSpace.single i 1))) j).trans
    (hcoeff i)
  simp only [map_sub, ContinuousLinearEquiv.symm_apply_apply, PiLp.sub_apply, Real.norm_eq_abs] at hpoint
  simpa only [Matrix.sub_apply, Matrix.one_apply, radialCoefficientMatrix,
    PiLp.single_apply, Pi.single_apply, eq_comm] using hpoint

end RegularPointCoordinates

end

end OAI
