import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL09

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_9 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 =
    lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_9_0_0
  · exact computeLDL_9_0_1
  · exact computeLDL_9_0_2
  · exact computeLDL_9_0_3
  · exact computeLDL_9_0_4
  · exact computeLDL_9_1_0
  · exact computeLDL_9_1_1
  · exact computeLDL_9_1_2
  · exact computeLDL_9_1_3
  · exact computeLDL_9_1_4
  · exact computeLDL_9_2_0
  · exact computeLDL_9_2_1
  · exact computeLDL_9_2_2
  · exact computeLDL_9_2_3
  · exact computeLDL_9_2_4
  · exact computeLDL_9_3_0
  · exact computeLDL_9_3_1
  · exact computeLDL_9_3_2
  · exact computeLDL_9_3_3
  · exact computeLDL_9_3_4
  · exact computeLDL_9_4_0
  · exact computeLDL_9_4_1
  · exact computeLDL_9_4_2
  · exact computeLDL_9_4_3
  · exact computeLDL_9_4_4

end Laughlin.Certificate

end OAI
