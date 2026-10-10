import OAI.Analysis.HyperbolicCones.ComplexPositive
import OAI.Analysis.HyperbolicCones.MatrixResolvent
import OAI.Analysis.HyperbolicCones.LineEvaluation

namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator ComplexOrder
open Matrix

namespace Paper256

theorem matrixValue_nonzero_nonreal (X Z : Sym 4) (y : Fin 3 → ℝ)
    (z : ℂ) (hz : z.im ≠ 0) :
    matrixValue (z • (1 : Mat 4 ℂ) - (X : Mat 4 ℝ).map Complex.ofReal)
      (z • (1 : Mat 4 ℂ) - (Z : Mat 4 ℝ).map Complex.ofReal)
      (fun i => -(y i : ℂ)) ≠ 0 := by
  have hu := complex_resolvent_isUnit (X : Mat 4 ℝ) X.property z hz
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hh := positive_map_resolvent_isUnit
    ((X : Mat 4 ℝ).map Complex.ofReal) ((Z : Mat 4 ℝ).map Complex.ofReal)
    (isHermitian_complexify _ X.property) (isHermitian_complexify _ Z.property)
    (phiLinear (fun i => ((-y) i : ℂ)))
    (fun M => phi_conjTranspose (-y) M)
    (fun M hM => phi_complex_posSemidef (-y) M hM) z hz
  change IsUnit (z • (1 : Mat 4 ℂ) - (Z : Mat 4 ℝ).map Complex.ofReal -
    phi (fun i => ((-y) i : ℂ))
      ((z • (1 : Mat 4 ℂ) - (X : Mat 4 ℝ).map Complex.ofReal)⁻¹)) at hh
  simp only [Pi.neg_apply, Complex.ofReal_neg] at hh
  rw [matrixValue_inverse _ _ _ hd]
  exact mul_ne_zero (pow_ne_zero 4 hd.ne_zero)
    ((Matrix.isUnit_iff_isUnit_det _).1 hh).ne_zero

theorem linePolynomial_complex_roots_real (x : Ambient) (z : ℂ)
    (hz : (linePolynomial x).aeval z = 0) : z.im = 0 := by
  rcases x with ⟨⟨X, Z⟩, y⟩
  by_contra hn
  apply matrixValue_nonzero_nonreal X Z y z hn
  change (linePolynomial ((X, Z), y)).eval₂ (algebraMap ℝ ℂ) z = 0 at hz
  rw [linePolynomial_eval₂] at hz
  exact hz

end Paper256

end

end OAI
