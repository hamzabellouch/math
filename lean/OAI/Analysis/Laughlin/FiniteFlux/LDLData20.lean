import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch20
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch20
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch20
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch20
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch20
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch20
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL06Batch20
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL07Batch20
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL08Batch20
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL09Batch20

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_20 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 =
    lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_20_0_0
  · exact computeLDL_20_0_1
  · exact computeLDL_20_0_2
  · exact computeLDL_20_0_3
  · exact computeLDL_20_0_4
  · exact computeLDL_20_0_5
  · exact computeLDL_20_0_6
  · exact computeLDL_20_0_7
  · exact computeLDL_20_0_8
  · exact computeLDL_20_0_9
  · exact computeLDL_20_1_0
  · exact computeLDL_20_1_1
  · exact computeLDL_20_1_2
  · exact computeLDL_20_1_3
  · exact computeLDL_20_1_4
  · exact computeLDL_20_1_5
  · exact computeLDL_20_1_6
  · exact computeLDL_20_1_7
  · exact computeLDL_20_1_8
  · exact computeLDL_20_1_9
  · exact computeLDL_20_2_0
  · exact computeLDL_20_2_1
  · exact computeLDL_20_2_2
  · exact computeLDL_20_2_3
  · exact computeLDL_20_2_4
  · exact computeLDL_20_2_5
  · exact computeLDL_20_2_6
  · exact computeLDL_20_2_7
  · exact computeLDL_20_2_8
  · exact computeLDL_20_2_9
  · exact computeLDL_20_3_0
  · exact computeLDL_20_3_1
  · exact computeLDL_20_3_2
  · exact computeLDL_20_3_3
  · exact computeLDL_20_3_4
  · exact computeLDL_20_3_5
  · exact computeLDL_20_3_6
  · exact computeLDL_20_3_7
  · exact computeLDL_20_3_8
  · exact computeLDL_20_3_9
  · exact computeLDL_20_4_0
  · exact computeLDL_20_4_1
  · exact computeLDL_20_4_2
  · exact computeLDL_20_4_3
  · exact computeLDL_20_4_4
  · exact computeLDL_20_4_5
  · exact computeLDL_20_4_6
  · exact computeLDL_20_4_7
  · exact computeLDL_20_4_8
  · exact computeLDL_20_4_9
  · exact computeLDL_20_5_0
  · exact computeLDL_20_5_1
  · exact computeLDL_20_5_2
  · exact computeLDL_20_5_3
  · exact computeLDL_20_5_4
  · exact computeLDL_20_5_5
  · exact computeLDL_20_5_6
  · exact computeLDL_20_5_7
  · exact computeLDL_20_5_8
  · exact computeLDL_20_5_9
  · exact computeLDL_20_6_0
  · exact computeLDL_20_6_1
  · exact computeLDL_20_6_2
  · exact computeLDL_20_6_3
  · exact computeLDL_20_6_4
  · exact computeLDL_20_6_5
  · exact computeLDL_20_6_6
  · exact computeLDL_20_6_7
  · exact computeLDL_20_6_8
  · exact computeLDL_20_6_9
  · exact computeLDL_20_7_0
  · exact computeLDL_20_7_1
  · exact computeLDL_20_7_2
  · exact computeLDL_20_7_3
  · exact computeLDL_20_7_4
  · exact computeLDL_20_7_5
  · exact computeLDL_20_7_6
  · exact computeLDL_20_7_7
  · exact computeLDL_20_7_8
  · exact computeLDL_20_7_9
  · exact computeLDL_20_8_0
  · exact computeLDL_20_8_1
  · exact computeLDL_20_8_2
  · exact computeLDL_20_8_3
  · exact computeLDL_20_8_4
  · exact computeLDL_20_8_5
  · exact computeLDL_20_8_6
  · exact computeLDL_20_8_7
  · exact computeLDL_20_8_8
  · exact computeLDL_20_8_9
  · exact computeLDL_20_9_0
  · exact computeLDL_20_9_1
  · exact computeLDL_20_9_2
  · exact computeLDL_20_9_3
  · exact computeLDL_20_9_4
  · exact computeLDL_20_9_5
  · exact computeLDL_20_9_6
  · exact computeLDL_20_9_7
  · exact computeLDL_20_9_8
  · exact computeLDL_20_9_9

end Laughlin.Certificate

end OAI
