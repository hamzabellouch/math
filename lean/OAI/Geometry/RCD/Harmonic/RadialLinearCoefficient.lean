import OAI.Geometry.RCD.Coordinates.RadialCoefficientMatrix
import OAI.Geometry.RCD.Coordinates.LinearRadialFits

namespace OAI

/-! # Covector operator control from the constructed radial rows -/

open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

/-- The covector operator uses the transpose of the matrix acting on
coordinate values. A dimension factor suffices to transport its norm
estimate, without making any symmetry assumption on the radial matrix. -/
theorem finiteCoefficientMap_relative_bound {n : ℕ}
    (N : Euclidean n ≃L[ℝ] Euclidean n) (coeff : Fin n → Euclidean n)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hbound : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (radialCoefficientMatrix N coeff) - ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤ epsilon) :
    ‖N.symm.toContinuousLinearMap.comp (finiteCoefficientMap coeff) -
      ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤ (n : ℝ) ^ 2 * epsilon := by
  apply euclidean_operator_norm_le_of_entries _ hepsilon
  intro i j
  have h := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (radialCoefficientMatrix N coeff) - ContinuousLinearMap.id ℝ (Euclidean n)).le_opNorm
      (EuclideanSpace.single i 1)
  have he : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (radialCoefficientMatrix N coeff) - ContinuousLinearMap.id ℝ (Euclidean n))
        (EuclideanSpace.single i 1)‖ ≤ epsilon := by
    apply h.trans
    simpa using hbound
  have hj := (PiLp.norm_apply_le
    ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (radialCoefficientMatrix N coeff) -
      ContinuousLinearMap.id ℝ (Euclidean n)) (EuclideanSpace.single i 1)) j).trans he
  simpa [ContinuousLinearMap.comp_apply, finiteCoefficientMap_single,
    Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct, radialCoefficientMatrix,
    PiLp.single_apply, eq_comm, Real.norm_eq_abs] using hj

end RegularPointCoordinates

end

end OAI
