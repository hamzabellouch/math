import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL06Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL07Batch15

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_15 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 =
    lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_15_0_0
  · exact computeLDL_15_0_1
  · exact computeLDL_15_0_2
  · exact computeLDL_15_0_3
  · exact computeLDL_15_0_4
  · exact computeLDL_15_0_5
  · exact computeLDL_15_0_6
  · exact computeLDL_15_0_7
  · exact computeLDL_15_1_0
  · exact computeLDL_15_1_1
  · exact computeLDL_15_1_2
  · exact computeLDL_15_1_3
  · exact computeLDL_15_1_4
  · exact computeLDL_15_1_5
  · exact computeLDL_15_1_6
  · exact computeLDL_15_1_7
  · exact computeLDL_15_2_0
  · exact computeLDL_15_2_1
  · exact computeLDL_15_2_2
  · exact computeLDL_15_2_3
  · exact computeLDL_15_2_4
  · exact computeLDL_15_2_5
  · exact computeLDL_15_2_6
  · exact computeLDL_15_2_7
  · exact computeLDL_15_3_0
  · exact computeLDL_15_3_1
  · exact computeLDL_15_3_2
  · exact computeLDL_15_3_3
  · exact computeLDL_15_3_4
  · exact computeLDL_15_3_5
  · exact computeLDL_15_3_6
  · exact computeLDL_15_3_7
  · exact computeLDL_15_4_0
  · exact computeLDL_15_4_1
  · exact computeLDL_15_4_2
  · exact computeLDL_15_4_3
  · exact computeLDL_15_4_4
  · exact computeLDL_15_4_5
  · exact computeLDL_15_4_6
  · exact computeLDL_15_4_7
  · exact computeLDL_15_5_0
  · exact computeLDL_15_5_1
  · exact computeLDL_15_5_2
  · exact computeLDL_15_5_3
  · exact computeLDL_15_5_4
  · exact computeLDL_15_5_5
  · exact computeLDL_15_5_6
  · exact computeLDL_15_5_7
  · exact computeLDL_15_6_0
  · exact computeLDL_15_6_1
  · exact computeLDL_15_6_2
  · exact computeLDL_15_6_3
  · exact computeLDL_15_6_4
  · exact computeLDL_15_6_5
  · exact computeLDL_15_6_6
  · exact computeLDL_15_6_7
  · exact computeLDL_15_7_0
  · exact computeLDL_15_7_1
  · exact computeLDL_15_7_2
  · exact computeLDL_15_7_3
  · exact computeLDL_15_7_4
  · exact computeLDL_15_7_5
  · exact computeLDL_15_7_6
  · exact computeLDL_15_7_7

end Laughlin.Certificate

end OAI
