import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch19
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch19
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch19
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch19
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch19
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch19
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL06Batch19
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL07Batch19
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL08Batch19
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL09Batch19

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_19 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 =
    lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_19_0_0
  · exact computeLDL_19_0_1
  · exact computeLDL_19_0_2
  · exact computeLDL_19_0_3
  · exact computeLDL_19_0_4
  · exact computeLDL_19_0_5
  · exact computeLDL_19_0_6
  · exact computeLDL_19_0_7
  · exact computeLDL_19_0_8
  · exact computeLDL_19_0_9
  · exact computeLDL_19_1_0
  · exact computeLDL_19_1_1
  · exact computeLDL_19_1_2
  · exact computeLDL_19_1_3
  · exact computeLDL_19_1_4
  · exact computeLDL_19_1_5
  · exact computeLDL_19_1_6
  · exact computeLDL_19_1_7
  · exact computeLDL_19_1_8
  · exact computeLDL_19_1_9
  · exact computeLDL_19_2_0
  · exact computeLDL_19_2_1
  · exact computeLDL_19_2_2
  · exact computeLDL_19_2_3
  · exact computeLDL_19_2_4
  · exact computeLDL_19_2_5
  · exact computeLDL_19_2_6
  · exact computeLDL_19_2_7
  · exact computeLDL_19_2_8
  · exact computeLDL_19_2_9
  · exact computeLDL_19_3_0
  · exact computeLDL_19_3_1
  · exact computeLDL_19_3_2
  · exact computeLDL_19_3_3
  · exact computeLDL_19_3_4
  · exact computeLDL_19_3_5
  · exact computeLDL_19_3_6
  · exact computeLDL_19_3_7
  · exact computeLDL_19_3_8
  · exact computeLDL_19_3_9
  · exact computeLDL_19_4_0
  · exact computeLDL_19_4_1
  · exact computeLDL_19_4_2
  · exact computeLDL_19_4_3
  · exact computeLDL_19_4_4
  · exact computeLDL_19_4_5
  · exact computeLDL_19_4_6
  · exact computeLDL_19_4_7
  · exact computeLDL_19_4_8
  · exact computeLDL_19_4_9
  · exact computeLDL_19_5_0
  · exact computeLDL_19_5_1
  · exact computeLDL_19_5_2
  · exact computeLDL_19_5_3
  · exact computeLDL_19_5_4
  · exact computeLDL_19_5_5
  · exact computeLDL_19_5_6
  · exact computeLDL_19_5_7
  · exact computeLDL_19_5_8
  · exact computeLDL_19_5_9
  · exact computeLDL_19_6_0
  · exact computeLDL_19_6_1
  · exact computeLDL_19_6_2
  · exact computeLDL_19_6_3
  · exact computeLDL_19_6_4
  · exact computeLDL_19_6_5
  · exact computeLDL_19_6_6
  · exact computeLDL_19_6_7
  · exact computeLDL_19_6_8
  · exact computeLDL_19_6_9
  · exact computeLDL_19_7_0
  · exact computeLDL_19_7_1
  · exact computeLDL_19_7_2
  · exact computeLDL_19_7_3
  · exact computeLDL_19_7_4
  · exact computeLDL_19_7_5
  · exact computeLDL_19_7_6
  · exact computeLDL_19_7_7
  · exact computeLDL_19_7_8
  · exact computeLDL_19_7_9
  · exact computeLDL_19_8_0
  · exact computeLDL_19_8_1
  · exact computeLDL_19_8_2
  · exact computeLDL_19_8_3
  · exact computeLDL_19_8_4
  · exact computeLDL_19_8_5
  · exact computeLDL_19_8_6
  · exact computeLDL_19_8_7
  · exact computeLDL_19_8_8
  · exact computeLDL_19_8_9
  · exact computeLDL_19_9_0
  · exact computeLDL_19_9_1
  · exact computeLDL_19_9_2
  · exact computeLDL_19_9_3
  · exact computeLDL_19_9_4
  · exact computeLDL_19_9_5
  · exact computeLDL_19_9_6
  · exact computeLDL_19_9_7
  · exact computeLDL_19_9_8
  · exact computeLDL_19_9_9

end Laughlin.Certificate

end OAI
