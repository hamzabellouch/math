import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL050511
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL11

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_11 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 =
    lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_11_0_0
  · exact computeLDL_11_0_1
  · exact computeLDL_11_0_2
  · exact computeLDL_11_0_3
  · exact computeLDL_11_0_4
  · exact computeLDL_11_0_5
  · exact computeLDL_11_1_0
  · exact computeLDL_11_1_1
  · exact computeLDL_11_1_2
  · exact computeLDL_11_1_3
  · exact computeLDL_11_1_4
  · exact computeLDL_11_1_5
  · exact computeLDL_11_2_0
  · exact computeLDL_11_2_1
  · exact computeLDL_11_2_2
  · exact computeLDL_11_2_3
  · exact computeLDL_11_2_4
  · exact computeLDL_11_2_5
  · exact computeLDL_11_3_0
  · exact computeLDL_11_3_1
  · exact computeLDL_11_3_2
  · exact computeLDL_11_3_3
  · exact computeLDL_11_3_4
  · exact computeLDL_11_3_5
  · exact computeLDL_11_4_0
  · exact computeLDL_11_4_1
  · exact computeLDL_11_4_2
  · exact computeLDL_11_4_3
  · exact computeLDL_11_4_4
  · exact computeLDL_11_4_5
  · exact computeLDL_11_5_0
  · exact computeLDL_11_5_1
  · exact computeLDL_11_5_2
  · exact computeLDL_11_5_3
  · exact computeLDL_11_5_4
  · exact computeLDL_11_5_5

end Laughlin.Certificate

end OAI
