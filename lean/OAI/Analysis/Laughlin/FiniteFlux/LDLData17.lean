import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL06Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL07Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL08Batch17

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_17 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 =
    lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_17_0_0
  · exact computeLDL_17_0_1
  · exact computeLDL_17_0_2
  · exact computeLDL_17_0_3
  · exact computeLDL_17_0_4
  · exact computeLDL_17_0_5
  · exact computeLDL_17_0_6
  · exact computeLDL_17_0_7
  · exact computeLDL_17_0_8
  · exact computeLDL_17_1_0
  · exact computeLDL_17_1_1
  · exact computeLDL_17_1_2
  · exact computeLDL_17_1_3
  · exact computeLDL_17_1_4
  · exact computeLDL_17_1_5
  · exact computeLDL_17_1_6
  · exact computeLDL_17_1_7
  · exact computeLDL_17_1_8
  · exact computeLDL_17_2_0
  · exact computeLDL_17_2_1
  · exact computeLDL_17_2_2
  · exact computeLDL_17_2_3
  · exact computeLDL_17_2_4
  · exact computeLDL_17_2_5
  · exact computeLDL_17_2_6
  · exact computeLDL_17_2_7
  · exact computeLDL_17_2_8
  · exact computeLDL_17_3_0
  · exact computeLDL_17_3_1
  · exact computeLDL_17_3_2
  · exact computeLDL_17_3_3
  · exact computeLDL_17_3_4
  · exact computeLDL_17_3_5
  · exact computeLDL_17_3_6
  · exact computeLDL_17_3_7
  · exact computeLDL_17_3_8
  · exact computeLDL_17_4_0
  · exact computeLDL_17_4_1
  · exact computeLDL_17_4_2
  · exact computeLDL_17_4_3
  · exact computeLDL_17_4_4
  · exact computeLDL_17_4_5
  · exact computeLDL_17_4_6
  · exact computeLDL_17_4_7
  · exact computeLDL_17_4_8
  · exact computeLDL_17_5_0
  · exact computeLDL_17_5_1
  · exact computeLDL_17_5_2
  · exact computeLDL_17_5_3
  · exact computeLDL_17_5_4
  · exact computeLDL_17_5_5
  · exact computeLDL_17_5_6
  · exact computeLDL_17_5_7
  · exact computeLDL_17_5_8
  · exact computeLDL_17_6_0
  · exact computeLDL_17_6_1
  · exact computeLDL_17_6_2
  · exact computeLDL_17_6_3
  · exact computeLDL_17_6_4
  · exact computeLDL_17_6_5
  · exact computeLDL_17_6_6
  · exact computeLDL_17_6_7
  · exact computeLDL_17_6_8
  · exact computeLDL_17_7_0
  · exact computeLDL_17_7_1
  · exact computeLDL_17_7_2
  · exact computeLDL_17_7_3
  · exact computeLDL_17_7_4
  · exact computeLDL_17_7_5
  · exact computeLDL_17_7_6
  · exact computeLDL_17_7_7
  · exact computeLDL_17_7_8
  · exact computeLDL_17_8_0
  · exact computeLDL_17_8_1
  · exact computeLDL_17_8_2
  · exact computeLDL_17_8_3
  · exact computeLDL_17_8_4
  · exact computeLDL_17_8_5
  · exact computeLDL_17_8_6
  · exact computeLDL_17_8_7
  · exact computeLDL_17_8_8

end Laughlin.Certificate

end OAI
