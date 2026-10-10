import OAI.Analysis.Laughlin.FiniteFlux.LDL08

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem ldl_8 : compressedRational 8 =
    lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact ldl_8_0_0
  · exact ldl_8_0_1
  · exact ldl_8_0_2
  · exact ldl_8_0_3
  · exact ldl_8_1_0
  · exact ldl_8_1_1
  · exact ldl_8_1_2
  · exact ldl_8_1_3
  · exact ldl_8_2_0
  · exact ldl_8_2_1
  · exact ldl_8_2_2
  · exact ldl_8_2_3
  · exact ldl_8_3_0
  · exact ldl_8_3_1
  · exact ldl_8_3_2
  · exact ldl_8_3_3
theorem four_body_8_positive :
    ((compressedRational 8).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_8 pivots_8 ldl_8
  intro i
  fin_cases i <;> norm_num [pivots_8]

end Laughlin.Certificate

end OAI
