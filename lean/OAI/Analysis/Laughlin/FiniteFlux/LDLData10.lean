import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL10

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_10 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 =
    lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_10_0_0
  · exact computeLDL_10_0_1
  · exact computeLDL_10_0_2
  · exact computeLDL_10_0_3
  · exact computeLDL_10_0_4
  · exact computeLDL_10_1_0
  · exact computeLDL_10_1_1
  · exact computeLDL_10_1_2
  · exact computeLDL_10_1_3
  · exact computeLDL_10_1_4
  · exact computeLDL_10_2_0
  · exact computeLDL_10_2_1
  · exact computeLDL_10_2_2
  · exact computeLDL_10_2_3
  · exact computeLDL_10_2_4
  · exact computeLDL_10_3_0
  · exact computeLDL_10_3_1
  · exact computeLDL_10_3_2
  · exact computeLDL_10_3_3
  · exact computeLDL_10_3_4
  · exact computeLDL_10_4_0
  · exact computeLDL_10_4_1
  · exact computeLDL_10_4_2
  · exact computeLDL_10_4_3
  · exact computeLDL_10_4_4

end Laughlin.Certificate

end OAI
