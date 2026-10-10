import OAI.Analysis.HyperbolicCones.LineEvaluation
import OAI.Analysis.HyperbolicCones.MatrixBasic

namespace OAI

noncomputable section

open Matrix Polynomial
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

theorem matrixValue_zero_parameter {K : Type u} [CommRing K] (X Z : Mat 4 K) :
    matrixValue X Z (0 : Fin 3 → K) = X.det ^ 4 * Z.det := by
  rw [matrixValue, phi_zero_parameter, sub_zero, Matrix.det_smul]
  rfl

theorem linePolynomial_zero_parameter (X Z : Sym 4) :
    linePolynomial ((X, Z), (0 : Fin 3 → ℝ)) =
      (X : Mat 4 ℝ).charpoly ^ 4 * (Z : Mat 4 ℝ).charpoly := by
  apply Polynomial.funext
  intro t
  have he := linePolynomial_eval₂ (RingHom.id ℝ) X Z (0 : Fin 3 → ℝ) t
  simp only [Polynomial.eval₂_id, RingHom.id_apply, Pi.zero_apply,
    neg_zero] at he
  rw [he]
  change matrixValue (t • 1 - (X : Mat 4 ℝ)) (t • 1 - (Z : Mat 4 ℝ))
    (0 : Fin 3 → ℝ) = _
  rw [matrixValue_zero_parameter]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Matrix.eval_charpoly]
  have hs : Matrix.scalar (Fin 4) t = t • (1 : Mat 4 ℝ) := by
    ext i j
    simp [Matrix.scalar, Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply]
  rw [hs]

theorem linePolynomial_repeated_roots :
    linePolynomial ((1, 0), 0) = (Polynomial.X - 1) ^ 16 * Polynomial.X ^ 4 := by
  rw [linePolynomial_zero_parameter]
  simp [Matrix.charpoly_one, Matrix.charpoly_zero, ← pow_mul]

theorem repeated_root_point_not_scalar_basePoint :
    ¬ ∃ t : ℝ, (((1, 0), 0) : Ambient) = t • basePoint := by
  rintro ⟨t, ht⟩
  have hx := congrArg (fun x : Ambient => (x.1.1 : Mat 4 ℝ) 0 0) ht
  have hz := congrArg (fun x : Ambient => (x.1.2 : Mat 4 ℝ) 0 0) ht
  simp [basePoint] at hx hz
  linarith

end Paper256

end

end OAI
