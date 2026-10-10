import OAI.Analysis.HyperbolicCones.ConeMatrix
import OAI.Analysis.HyperbolicCones.PolynomialEvaluation

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem ambient_shift (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ) :
    (((X, Z), y) : Ambient) + t • basePoint = ((X + t • 1, Z + t • 1), y) := by
  simp [basePoint]

theorem polynomial_shift_inverse (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ)
    (ht : ((X + t • 1 : Sym 4) : Mat 4 ℝ).PosDef) :
    MvPolynomial.eval (coordinates ((((X, Z), y) : Ambient) + t • basePoint)) polynomial =
      ((X + t • 1 : Sym 4) : Mat 4 ℝ).det ^ 4 *
        (coneResidual X Z y t : Mat 4 ℝ).det := by
  rw [ambient_shift, polynomial_evaluation]
  exact matrixValue_inverse _ _ _ ((Matrix.isUnit_iff_isUnit_det _).mp ht.isUnit)

end Paper256

end

end OAI
