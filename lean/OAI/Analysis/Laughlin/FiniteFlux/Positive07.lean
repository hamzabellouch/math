import OAI.Analysis.Laughlin.FiniteFlux.Error07
import OAI.Analysis.Laughlin.FiniteFlux.Gram07
import OAI.Analysis.Laughlin.FourBody.Matrix

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
def lower_7 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
    0, 1, 0, 0;
    -1/4, 0, 1, 0;
    7/4, 0, 0, 1]
def pivots_7 : Fin 4 → ℚ :=
  ![4554569876705321270859037803/751619276800000000000000, 0, 0, 0]

theorem ldl_7 : compressedRational 7 =
    lower_7 * Matrix.diagonal pivots_7 * lower_7.transpose := by
  unfold compressedRational middleRational
  rw [gram_7, error_7]
  decide +kernel
theorem four_body_7_positive :
    ((compressedRational 7).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_7 pivots_7 ldl_7
  intro i
  fin_cases i <;> norm_num [pivots_7]

end Laughlin.Certificate

end OAI
