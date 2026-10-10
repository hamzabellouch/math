import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL06Batch13

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_13 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 =
    lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_13_0_0
  · exact computeLDL_13_0_1
  · exact computeLDL_13_0_2
  · exact computeLDL_13_0_3
  · exact computeLDL_13_0_4
  · exact computeLDL_13_0_5
  · exact computeLDL_13_0_6
  · exact computeLDL_13_1_0
  · exact computeLDL_13_1_1
  · exact computeLDL_13_1_2
  · exact computeLDL_13_1_3
  · exact computeLDL_13_1_4
  · exact computeLDL_13_1_5
  · exact computeLDL_13_1_6
  · exact computeLDL_13_2_0
  · exact computeLDL_13_2_1
  · exact computeLDL_13_2_2
  · exact computeLDL_13_2_3
  · exact computeLDL_13_2_4
  · exact computeLDL_13_2_5
  · exact computeLDL_13_2_6
  · exact computeLDL_13_3_0
  · exact computeLDL_13_3_1
  · exact computeLDL_13_3_2
  · exact computeLDL_13_3_3
  · exact computeLDL_13_3_4
  · exact computeLDL_13_3_5
  · exact computeLDL_13_3_6
  · exact computeLDL_13_4_0
  · exact computeLDL_13_4_1
  · exact computeLDL_13_4_2
  · exact computeLDL_13_4_3
  · exact computeLDL_13_4_4
  · exact computeLDL_13_4_5
  · exact computeLDL_13_4_6
  · exact computeLDL_13_5_0
  · exact computeLDL_13_5_1
  · exact computeLDL_13_5_2
  · exact computeLDL_13_5_3
  · exact computeLDL_13_5_4
  · exact computeLDL_13_5_5
  · exact computeLDL_13_5_6
  · exact computeLDL_13_6_0
  · exact computeLDL_13_6_1
  · exact computeLDL_13_6_2
  · exact computeLDL_13_6_3
  · exact computeLDL_13_6_4
  · exact computeLDL_13_6_5
  · exact computeLDL_13_6_6

end Laughlin.Certificate

end OAI
