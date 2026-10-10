import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL06Batch14

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_14 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 =
    lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_14_0_0
  · exact computeLDL_14_0_1
  · exact computeLDL_14_0_2
  · exact computeLDL_14_0_3
  · exact computeLDL_14_0_4
  · exact computeLDL_14_0_5
  · exact computeLDL_14_0_6
  · exact computeLDL_14_1_0
  · exact computeLDL_14_1_1
  · exact computeLDL_14_1_2
  · exact computeLDL_14_1_3
  · exact computeLDL_14_1_4
  · exact computeLDL_14_1_5
  · exact computeLDL_14_1_6
  · exact computeLDL_14_2_0
  · exact computeLDL_14_2_1
  · exact computeLDL_14_2_2
  · exact computeLDL_14_2_3
  · exact computeLDL_14_2_4
  · exact computeLDL_14_2_5
  · exact computeLDL_14_2_6
  · exact computeLDL_14_3_0
  · exact computeLDL_14_3_1
  · exact computeLDL_14_3_2
  · exact computeLDL_14_3_3
  · exact computeLDL_14_3_4
  · exact computeLDL_14_3_5
  · exact computeLDL_14_3_6
  · exact computeLDL_14_4_0
  · exact computeLDL_14_4_1
  · exact computeLDL_14_4_2
  · exact computeLDL_14_4_3
  · exact computeLDL_14_4_4
  · exact computeLDL_14_4_5
  · exact computeLDL_14_4_6
  · exact computeLDL_14_5_0
  · exact computeLDL_14_5_1
  · exact computeLDL_14_5_2
  · exact computeLDL_14_5_3
  · exact computeLDL_14_5_4
  · exact computeLDL_14_5_5
  · exact computeLDL_14_5_6
  · exact computeLDL_14_6_0
  · exact computeLDL_14_6_1
  · exact computeLDL_14_6_2
  · exact computeLDL_14_6_3
  · exact computeLDL_14_6_4
  · exact computeLDL_14_6_5
  · exact computeLDL_14_6_6

end Laughlin.Certificate

end OAI
