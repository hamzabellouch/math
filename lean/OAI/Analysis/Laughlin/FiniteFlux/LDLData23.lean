import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch23
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch23
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch23
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch23
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch23
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch23
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL06Batch23
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL07Batch23
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL08Batch23
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL09Batch23
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL10Batch23
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL11Batch23

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_23 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 =
    lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_23_0_0
  · exact computeLDL_23_0_1
  · exact computeLDL_23_0_2
  · exact computeLDL_23_0_3
  · exact computeLDL_23_0_4
  · exact computeLDL_23_0_5
  · exact computeLDL_23_0_6
  · exact computeLDL_23_0_7
  · exact computeLDL_23_0_8
  · exact computeLDL_23_0_9
  · exact computeLDL_23_0_10
  · exact computeLDL_23_0_11
  · exact computeLDL_23_1_0
  · exact computeLDL_23_1_1
  · exact computeLDL_23_1_2
  · exact computeLDL_23_1_3
  · exact computeLDL_23_1_4
  · exact computeLDL_23_1_5
  · exact computeLDL_23_1_6
  · exact computeLDL_23_1_7
  · exact computeLDL_23_1_8
  · exact computeLDL_23_1_9
  · exact computeLDL_23_1_10
  · exact computeLDL_23_1_11
  · exact computeLDL_23_2_0
  · exact computeLDL_23_2_1
  · exact computeLDL_23_2_2
  · exact computeLDL_23_2_3
  · exact computeLDL_23_2_4
  · exact computeLDL_23_2_5
  · exact computeLDL_23_2_6
  · exact computeLDL_23_2_7
  · exact computeLDL_23_2_8
  · exact computeLDL_23_2_9
  · exact computeLDL_23_2_10
  · exact computeLDL_23_2_11
  · exact computeLDL_23_3_0
  · exact computeLDL_23_3_1
  · exact computeLDL_23_3_2
  · exact computeLDL_23_3_3
  · exact computeLDL_23_3_4
  · exact computeLDL_23_3_5
  · exact computeLDL_23_3_6
  · exact computeLDL_23_3_7
  · exact computeLDL_23_3_8
  · exact computeLDL_23_3_9
  · exact computeLDL_23_3_10
  · exact computeLDL_23_3_11
  · exact computeLDL_23_4_0
  · exact computeLDL_23_4_1
  · exact computeLDL_23_4_2
  · exact computeLDL_23_4_3
  · exact computeLDL_23_4_4
  · exact computeLDL_23_4_5
  · exact computeLDL_23_4_6
  · exact computeLDL_23_4_7
  · exact computeLDL_23_4_8
  · exact computeLDL_23_4_9
  · exact computeLDL_23_4_10
  · exact computeLDL_23_4_11
  · exact computeLDL_23_5_0
  · exact computeLDL_23_5_1
  · exact computeLDL_23_5_2
  · exact computeLDL_23_5_3
  · exact computeLDL_23_5_4
  · exact computeLDL_23_5_5
  · exact computeLDL_23_5_6
  · exact computeLDL_23_5_7
  · exact computeLDL_23_5_8
  · exact computeLDL_23_5_9
  · exact computeLDL_23_5_10
  · exact computeLDL_23_5_11
  · exact computeLDL_23_6_0
  · exact computeLDL_23_6_1
  · exact computeLDL_23_6_2
  · exact computeLDL_23_6_3
  · exact computeLDL_23_6_4
  · exact computeLDL_23_6_5
  · exact computeLDL_23_6_6
  · exact computeLDL_23_6_7
  · exact computeLDL_23_6_8
  · exact computeLDL_23_6_9
  · exact computeLDL_23_6_10
  · exact computeLDL_23_6_11
  · exact computeLDL_23_7_0
  · exact computeLDL_23_7_1
  · exact computeLDL_23_7_2
  · exact computeLDL_23_7_3
  · exact computeLDL_23_7_4
  · exact computeLDL_23_7_5
  · exact computeLDL_23_7_6
  · exact computeLDL_23_7_7
  · exact computeLDL_23_7_8
  · exact computeLDL_23_7_9
  · exact computeLDL_23_7_10
  · exact computeLDL_23_7_11
  · exact computeLDL_23_8_0
  · exact computeLDL_23_8_1
  · exact computeLDL_23_8_2
  · exact computeLDL_23_8_3
  · exact computeLDL_23_8_4
  · exact computeLDL_23_8_5
  · exact computeLDL_23_8_6
  · exact computeLDL_23_8_7
  · exact computeLDL_23_8_8
  · exact computeLDL_23_8_9
  · exact computeLDL_23_8_10
  · exact computeLDL_23_8_11
  · exact computeLDL_23_9_0
  · exact computeLDL_23_9_1
  · exact computeLDL_23_9_2
  · exact computeLDL_23_9_3
  · exact computeLDL_23_9_4
  · exact computeLDL_23_9_5
  · exact computeLDL_23_9_6
  · exact computeLDL_23_9_7
  · exact computeLDL_23_9_8
  · exact computeLDL_23_9_9
  · exact computeLDL_23_9_10
  · exact computeLDL_23_9_11
  · exact computeLDL_23_10_0
  · exact computeLDL_23_10_1
  · exact computeLDL_23_10_2
  · exact computeLDL_23_10_3
  · exact computeLDL_23_10_4
  · exact computeLDL_23_10_5
  · exact computeLDL_23_10_6
  · exact computeLDL_23_10_7
  · exact computeLDL_23_10_8
  · exact computeLDL_23_10_9
  · exact computeLDL_23_10_10
  · exact computeLDL_23_10_11
  · exact computeLDL_23_11_0
  · exact computeLDL_23_11_1
  · exact computeLDL_23_11_2
  · exact computeLDL_23_11_3
  · exact computeLDL_23_11_4
  · exact computeLDL_23_11_5
  · exact computeLDL_23_11_6
  · exact computeLDL_23_11_7
  · exact computeLDL_23_11_8
  · exact computeLDL_23_11_9
  · exact computeLDL_23_11_10
  · exact computeLDL_23_11_11

end Laughlin.Certificate

end OAI
