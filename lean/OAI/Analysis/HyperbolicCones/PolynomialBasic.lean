import OAI.Analysis.HyperbolicCones.PolynomialHomogeneous
import OAI.Analysis.HyperbolicCones.PolynomialEvaluation
import OAI.Analysis.HyperbolicCones.MatrixBasic

namespace OAI

noncomputable section

open Matrix MvPolynomial
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem polynomial_basePoint : MvPolynomial.eval (coordinates basePoint) polynomial = 1 := by
  change MvPolynomial.eval (coordinates (((1 : Sym 4), 1), 0)) polynomial = 1
  rw [polynomial_evaluation]
  simp [matrixValue, phi_zero_parameter]

theorem polynomial_ne_zero : polynomial ≠ 0 := by
  intro h
  have hp := polynomial_basePoint
  simp [h] at hp

theorem polynomial_totalDegree : polynomial.totalDegree = 20 :=
  polynomial_homogeneous.totalDegree polynomial_ne_zero

end Paper256

end

end OAI
