import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL06Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL07Batch16

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_16 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 =
    lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_16_0_0
  · exact computeLDL_16_0_1
  · exact computeLDL_16_0_2
  · exact computeLDL_16_0_3
  · exact computeLDL_16_0_4
  · exact computeLDL_16_0_5
  · exact computeLDL_16_0_6
  · exact computeLDL_16_0_7
  · exact computeLDL_16_1_0
  · exact computeLDL_16_1_1
  · exact computeLDL_16_1_2
  · exact computeLDL_16_1_3
  · exact computeLDL_16_1_4
  · exact computeLDL_16_1_5
  · exact computeLDL_16_1_6
  · exact computeLDL_16_1_7
  · exact computeLDL_16_2_0
  · exact computeLDL_16_2_1
  · exact computeLDL_16_2_2
  · exact computeLDL_16_2_3
  · exact computeLDL_16_2_4
  · exact computeLDL_16_2_5
  · exact computeLDL_16_2_6
  · exact computeLDL_16_2_7
  · exact computeLDL_16_3_0
  · exact computeLDL_16_3_1
  · exact computeLDL_16_3_2
  · exact computeLDL_16_3_3
  · exact computeLDL_16_3_4
  · exact computeLDL_16_3_5
  · exact computeLDL_16_3_6
  · exact computeLDL_16_3_7
  · exact computeLDL_16_4_0
  · exact computeLDL_16_4_1
  · exact computeLDL_16_4_2
  · exact computeLDL_16_4_3
  · exact computeLDL_16_4_4
  · exact computeLDL_16_4_5
  · exact computeLDL_16_4_6
  · exact computeLDL_16_4_7
  · exact computeLDL_16_5_0
  · exact computeLDL_16_5_1
  · exact computeLDL_16_5_2
  · exact computeLDL_16_5_3
  · exact computeLDL_16_5_4
  · exact computeLDL_16_5_5
  · exact computeLDL_16_5_6
  · exact computeLDL_16_5_7
  · exact computeLDL_16_6_0
  · exact computeLDL_16_6_1
  · exact computeLDL_16_6_2
  · exact computeLDL_16_6_3
  · exact computeLDL_16_6_4
  · exact computeLDL_16_6_5
  · exact computeLDL_16_6_6
  · exact computeLDL_16_6_7
  · exact computeLDL_16_7_0
  · exact computeLDL_16_7_1
  · exact computeLDL_16_7_2
  · exact computeLDL_16_7_3
  · exact computeLDL_16_7_4
  · exact computeLDL_16_7_5
  · exact computeLDL_16_7_6
  · exact computeLDL_16_7_7

end Laughlin.Certificate

end OAI
