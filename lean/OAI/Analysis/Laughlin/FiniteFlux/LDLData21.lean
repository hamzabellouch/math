import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch21
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch21
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch21
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch21
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch21
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch21
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL06Batch21
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL07Batch21
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL08Batch21
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL09Batch21
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL10Batch21

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_21 : MatrixCompute.compressed 21 candidateY_21 candidateZ_21 =
    lower_21 * Matrix.diagonal pivots_21 * lower_21.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_21_0_0
  · exact computeLDL_21_0_1
  · exact computeLDL_21_0_2
  · exact computeLDL_21_0_3
  · exact computeLDL_21_0_4
  · exact computeLDL_21_0_5
  · exact computeLDL_21_0_6
  · exact computeLDL_21_0_7
  · exact computeLDL_21_0_8
  · exact computeLDL_21_0_9
  · exact computeLDL_21_0_10
  · exact computeLDL_21_1_0
  · exact computeLDL_21_1_1
  · exact computeLDL_21_1_2
  · exact computeLDL_21_1_3
  · exact computeLDL_21_1_4
  · exact computeLDL_21_1_5
  · exact computeLDL_21_1_6
  · exact computeLDL_21_1_7
  · exact computeLDL_21_1_8
  · exact computeLDL_21_1_9
  · exact computeLDL_21_1_10
  · exact computeLDL_21_2_0
  · exact computeLDL_21_2_1
  · exact computeLDL_21_2_2
  · exact computeLDL_21_2_3
  · exact computeLDL_21_2_4
  · exact computeLDL_21_2_5
  · exact computeLDL_21_2_6
  · exact computeLDL_21_2_7
  · exact computeLDL_21_2_8
  · exact computeLDL_21_2_9
  · exact computeLDL_21_2_10
  · exact computeLDL_21_3_0
  · exact computeLDL_21_3_1
  · exact computeLDL_21_3_2
  · exact computeLDL_21_3_3
  · exact computeLDL_21_3_4
  · exact computeLDL_21_3_5
  · exact computeLDL_21_3_6
  · exact computeLDL_21_3_7
  · exact computeLDL_21_3_8
  · exact computeLDL_21_3_9
  · exact computeLDL_21_3_10
  · exact computeLDL_21_4_0
  · exact computeLDL_21_4_1
  · exact computeLDL_21_4_2
  · exact computeLDL_21_4_3
  · exact computeLDL_21_4_4
  · exact computeLDL_21_4_5
  · exact computeLDL_21_4_6
  · exact computeLDL_21_4_7
  · exact computeLDL_21_4_8
  · exact computeLDL_21_4_9
  · exact computeLDL_21_4_10
  · exact computeLDL_21_5_0
  · exact computeLDL_21_5_1
  · exact computeLDL_21_5_2
  · exact computeLDL_21_5_3
  · exact computeLDL_21_5_4
  · exact computeLDL_21_5_5
  · exact computeLDL_21_5_6
  · exact computeLDL_21_5_7
  · exact computeLDL_21_5_8
  · exact computeLDL_21_5_9
  · exact computeLDL_21_5_10
  · exact computeLDL_21_6_0
  · exact computeLDL_21_6_1
  · exact computeLDL_21_6_2
  · exact computeLDL_21_6_3
  · exact computeLDL_21_6_4
  · exact computeLDL_21_6_5
  · exact computeLDL_21_6_6
  · exact computeLDL_21_6_7
  · exact computeLDL_21_6_8
  · exact computeLDL_21_6_9
  · exact computeLDL_21_6_10
  · exact computeLDL_21_7_0
  · exact computeLDL_21_7_1
  · exact computeLDL_21_7_2
  · exact computeLDL_21_7_3
  · exact computeLDL_21_7_4
  · exact computeLDL_21_7_5
  · exact computeLDL_21_7_6
  · exact computeLDL_21_7_7
  · exact computeLDL_21_7_8
  · exact computeLDL_21_7_9
  · exact computeLDL_21_7_10
  · exact computeLDL_21_8_0
  · exact computeLDL_21_8_1
  · exact computeLDL_21_8_2
  · exact computeLDL_21_8_3
  · exact computeLDL_21_8_4
  · exact computeLDL_21_8_5
  · exact computeLDL_21_8_6
  · exact computeLDL_21_8_7
  · exact computeLDL_21_8_8
  · exact computeLDL_21_8_9
  · exact computeLDL_21_8_10
  · exact computeLDL_21_9_0
  · exact computeLDL_21_9_1
  · exact computeLDL_21_9_2
  · exact computeLDL_21_9_3
  · exact computeLDL_21_9_4
  · exact computeLDL_21_9_5
  · exact computeLDL_21_9_6
  · exact computeLDL_21_9_7
  · exact computeLDL_21_9_8
  · exact computeLDL_21_9_9
  · exact computeLDL_21_9_10
  · exact computeLDL_21_10_0
  · exact computeLDL_21_10_1
  · exact computeLDL_21_10_2
  · exact computeLDL_21_10_3
  · exact computeLDL_21_10_4
  · exact computeLDL_21_10_5
  · exact computeLDL_21_10_6
  · exact computeLDL_21_10_7
  · exact computeLDL_21_10_8
  · exact computeLDL_21_10_9
  · exact computeLDL_21_10_10

end Laughlin.Certificate

end OAI
