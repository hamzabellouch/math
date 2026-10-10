import OAI.Probability.InvariantIsing.Haar.HaarPolynomialCurve

namespace OAI

/-! Polynomial differentiation along the actual special-orthogonal rotations. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.Frobenius
namespace InvariantIsing

/-- Coordinate evaluation in the Frobenius matrix space. -/
def haarMatrixCoordinate {N : ℕ} (i j : Fin N) :
    Matrix (Fin N) (Fin N) ℝ →L[ℝ] ℝ :=
  (show Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ from
    { toFun := fun M => M i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }).toContinuousLinearMap

lemma hasDerivAt_specialPlaneRotation_entry {N : ℕ}
    (i j k l : Fin N) (U : SpecialOrthogonal N) (t : ℝ) :
    HasDerivAt (fun s => ((specialPlaneRotation i j s*U : SpecialOrthogonal N) :
        Matrix (Fin N) (Fin N) ℝ) k l)
      ((planeGenerator i j*((specialPlaneRotation i j t*U : SpecialOrthogonal N) :
        Matrix (Fin N) (Fin N) ℝ)) k l) t := by
  let A := planeGenerator i j
  let ev := haarMatrixCoordinate k l
  have hd := ev.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_exp_smul_const' A t).mul_const (U : Matrix (Fin N) (Fin N) ℝ))
  convert hd using 1
  · rfl
  · change (A*(NormedSpace.exp (t • A)*(U : Matrix (Fin N) (Fin N) ℝ))) k l =
      (A*NormedSpace.exp (t • A)*(U : Matrix (Fin N) (Fin N) ℝ)) k l
    rw [mul_assoc]

theorem hasDerivAt_specialPlaneRotation_polynomial {N : ℕ}
    (p : MatrixPolynomial N) (i j : Fin N) (U : SpecialOrthogonal N) (t : ℝ) :
    HasDerivAt (fun s => matrixPolynomialEval
        ((specialPlaneRotation i j s*U : SpecialOrthogonal N) :
          Matrix (Fin N) (Fin N) ℝ) p)
      (matrixPolynomialEval
        ((specialPlaneRotation i j t*U : SpecialOrthogonal N) :
          Matrix (Fin N) (Fin N) ℝ)
        (matrixPolynomialDerivation (planeGenerator i j) p)) t :=
  hasDerivAt_matrixPolynomialEval p _ _ t
    (fun k l => hasDerivAt_specialPlaneRotation_entry i j k l U t)

end InvariantIsing

end

end OAI
