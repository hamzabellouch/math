import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch22
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch22
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch22
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch22
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch22
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch22
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL06Batch22
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL07Batch22
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL08Batch22
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL09Batch22
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL10Batch22

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_22 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 =
    lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_22_0_0
  · exact computeLDL_22_0_1
  · exact computeLDL_22_0_2
  · exact computeLDL_22_0_3
  · exact computeLDL_22_0_4
  · exact computeLDL_22_0_5
  · exact computeLDL_22_0_6
  · exact computeLDL_22_0_7
  · exact computeLDL_22_0_8
  · exact computeLDL_22_0_9
  · exact computeLDL_22_0_10
  · exact computeLDL_22_1_0
  · exact computeLDL_22_1_1
  · exact computeLDL_22_1_2
  · exact computeLDL_22_1_3
  · exact computeLDL_22_1_4
  · exact computeLDL_22_1_5
  · exact computeLDL_22_1_6
  · exact computeLDL_22_1_7
  · exact computeLDL_22_1_8
  · exact computeLDL_22_1_9
  · exact computeLDL_22_1_10
  · exact computeLDL_22_2_0
  · exact computeLDL_22_2_1
  · exact computeLDL_22_2_2
  · exact computeLDL_22_2_3
  · exact computeLDL_22_2_4
  · exact computeLDL_22_2_5
  · exact computeLDL_22_2_6
  · exact computeLDL_22_2_7
  · exact computeLDL_22_2_8
  · exact computeLDL_22_2_9
  · exact computeLDL_22_2_10
  · exact computeLDL_22_3_0
  · exact computeLDL_22_3_1
  · exact computeLDL_22_3_2
  · exact computeLDL_22_3_3
  · exact computeLDL_22_3_4
  · exact computeLDL_22_3_5
  · exact computeLDL_22_3_6
  · exact computeLDL_22_3_7
  · exact computeLDL_22_3_8
  · exact computeLDL_22_3_9
  · exact computeLDL_22_3_10
  · exact computeLDL_22_4_0
  · exact computeLDL_22_4_1
  · exact computeLDL_22_4_2
  · exact computeLDL_22_4_3
  · exact computeLDL_22_4_4
  · exact computeLDL_22_4_5
  · exact computeLDL_22_4_6
  · exact computeLDL_22_4_7
  · exact computeLDL_22_4_8
  · exact computeLDL_22_4_9
  · exact computeLDL_22_4_10
  · exact computeLDL_22_5_0
  · exact computeLDL_22_5_1
  · exact computeLDL_22_5_2
  · exact computeLDL_22_5_3
  · exact computeLDL_22_5_4
  · exact computeLDL_22_5_5
  · exact computeLDL_22_5_6
  · exact computeLDL_22_5_7
  · exact computeLDL_22_5_8
  · exact computeLDL_22_5_9
  · exact computeLDL_22_5_10
  · exact computeLDL_22_6_0
  · exact computeLDL_22_6_1
  · exact computeLDL_22_6_2
  · exact computeLDL_22_6_3
  · exact computeLDL_22_6_4
  · exact computeLDL_22_6_5
  · exact computeLDL_22_6_6
  · exact computeLDL_22_6_7
  · exact computeLDL_22_6_8
  · exact computeLDL_22_6_9
  · exact computeLDL_22_6_10
  · exact computeLDL_22_7_0
  · exact computeLDL_22_7_1
  · exact computeLDL_22_7_2
  · exact computeLDL_22_7_3
  · exact computeLDL_22_7_4
  · exact computeLDL_22_7_5
  · exact computeLDL_22_7_6
  · exact computeLDL_22_7_7
  · exact computeLDL_22_7_8
  · exact computeLDL_22_7_9
  · exact computeLDL_22_7_10
  · exact computeLDL_22_8_0
  · exact computeLDL_22_8_1
  · exact computeLDL_22_8_2
  · exact computeLDL_22_8_3
  · exact computeLDL_22_8_4
  · exact computeLDL_22_8_5
  · exact computeLDL_22_8_6
  · exact computeLDL_22_8_7
  · exact computeLDL_22_8_8
  · exact computeLDL_22_8_9
  · exact computeLDL_22_8_10
  · exact computeLDL_22_9_0
  · exact computeLDL_22_9_1
  · exact computeLDL_22_9_2
  · exact computeLDL_22_9_3
  · exact computeLDL_22_9_4
  · exact computeLDL_22_9_5
  · exact computeLDL_22_9_6
  · exact computeLDL_22_9_7
  · exact computeLDL_22_9_8
  · exact computeLDL_22_9_9
  · exact computeLDL_22_9_10
  · exact computeLDL_22_10_0
  · exact computeLDL_22_10_1
  · exact computeLDL_22_10_2
  · exact computeLDL_22_10_3
  · exact computeLDL_22_10_4
  · exact computeLDL_22_10_5
  · exact computeLDL_22_10_6
  · exact computeLDL_22_10_7
  · exact computeLDL_22_10_8
  · exact computeLDL_22_10_9
  · exact computeLDL_22_10_10

end Laughlin.Certificate

end OAI
