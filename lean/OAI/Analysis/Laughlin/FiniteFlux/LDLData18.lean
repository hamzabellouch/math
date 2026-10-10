import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL06Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL07Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL08Batch18

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_18 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 =
    lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_18_0_0
  · exact computeLDL_18_0_1
  · exact computeLDL_18_0_2
  · exact computeLDL_18_0_3
  · exact computeLDL_18_0_4
  · exact computeLDL_18_0_5
  · exact computeLDL_18_0_6
  · exact computeLDL_18_0_7
  · exact computeLDL_18_0_8
  · exact computeLDL_18_1_0
  · exact computeLDL_18_1_1
  · exact computeLDL_18_1_2
  · exact computeLDL_18_1_3
  · exact computeLDL_18_1_4
  · exact computeLDL_18_1_5
  · exact computeLDL_18_1_6
  · exact computeLDL_18_1_7
  · exact computeLDL_18_1_8
  · exact computeLDL_18_2_0
  · exact computeLDL_18_2_1
  · exact computeLDL_18_2_2
  · exact computeLDL_18_2_3
  · exact computeLDL_18_2_4
  · exact computeLDL_18_2_5
  · exact computeLDL_18_2_6
  · exact computeLDL_18_2_7
  · exact computeLDL_18_2_8
  · exact computeLDL_18_3_0
  · exact computeLDL_18_3_1
  · exact computeLDL_18_3_2
  · exact computeLDL_18_3_3
  · exact computeLDL_18_3_4
  · exact computeLDL_18_3_5
  · exact computeLDL_18_3_6
  · exact computeLDL_18_3_7
  · exact computeLDL_18_3_8
  · exact computeLDL_18_4_0
  · exact computeLDL_18_4_1
  · exact computeLDL_18_4_2
  · exact computeLDL_18_4_3
  · exact computeLDL_18_4_4
  · exact computeLDL_18_4_5
  · exact computeLDL_18_4_6
  · exact computeLDL_18_4_7
  · exact computeLDL_18_4_8
  · exact computeLDL_18_5_0
  · exact computeLDL_18_5_1
  · exact computeLDL_18_5_2
  · exact computeLDL_18_5_3
  · exact computeLDL_18_5_4
  · exact computeLDL_18_5_5
  · exact computeLDL_18_5_6
  · exact computeLDL_18_5_7
  · exact computeLDL_18_5_8
  · exact computeLDL_18_6_0
  · exact computeLDL_18_6_1
  · exact computeLDL_18_6_2
  · exact computeLDL_18_6_3
  · exact computeLDL_18_6_4
  · exact computeLDL_18_6_5
  · exact computeLDL_18_6_6
  · exact computeLDL_18_6_7
  · exact computeLDL_18_6_8
  · exact computeLDL_18_7_0
  · exact computeLDL_18_7_1
  · exact computeLDL_18_7_2
  · exact computeLDL_18_7_3
  · exact computeLDL_18_7_4
  · exact computeLDL_18_7_5
  · exact computeLDL_18_7_6
  · exact computeLDL_18_7_7
  · exact computeLDL_18_7_8
  · exact computeLDL_18_8_0
  · exact computeLDL_18_8_1
  · exact computeLDL_18_8_2
  · exact computeLDL_18_8_3
  · exact computeLDL_18_8_4
  · exact computeLDL_18_8_5
  · exact computeLDL_18_8_6
  · exact computeLDL_18_8_7
  · exact computeLDL_18_8_8

end Laughlin.Certificate

end OAI
