import OAI.Analysis.Laughlin.FiniteFlux.Error05
import OAI.Analysis.Laughlin.FourBody.Matrix

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

def lowerFive : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0; -1/2, 1, 0; 5/4, 0, 1]

def pivotsFive : Fin 3 → ℚ :=
  ![56737668577815655510619653/300647710720000000000000, 0, 0]


theorem ldl_five : compressedRational 5 =
    lowerFive * Matrix.diagonal pivotsFive * lowerFive.transpose := by
  unfold compressedRational middleRational
  rw [gram_five, error_five]
  decide +kernel

theorem four_body_five_positive :
    ((compressedRational 5).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lowerFive pivotsFive ldl_five
  intro i
  fin_cases i <;> norm_num [pivotsFive]

end Laughlin.Certificate

end OAI
