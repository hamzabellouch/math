import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL00Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL01Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL02Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL03Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL04Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeLDL05Batch12

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_12 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 =
    lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_12_0_0
  · exact computeLDL_12_0_1
  · exact computeLDL_12_0_2
  · exact computeLDL_12_0_3
  · exact computeLDL_12_0_4
  · exact computeLDL_12_0_5
  · exact computeLDL_12_1_0
  · exact computeLDL_12_1_1
  · exact computeLDL_12_1_2
  · exact computeLDL_12_1_3
  · exact computeLDL_12_1_4
  · exact computeLDL_12_1_5
  · exact computeLDL_12_2_0
  · exact computeLDL_12_2_1
  · exact computeLDL_12_2_2
  · exact computeLDL_12_2_3
  · exact computeLDL_12_2_4
  · exact computeLDL_12_2_5
  · exact computeLDL_12_3_0
  · exact computeLDL_12_3_1
  · exact computeLDL_12_3_2
  · exact computeLDL_12_3_3
  · exact computeLDL_12_3_4
  · exact computeLDL_12_3_5
  · exact computeLDL_12_4_0
  · exact computeLDL_12_4_1
  · exact computeLDL_12_4_2
  · exact computeLDL_12_4_3
  · exact computeLDL_12_4_4
  · exact computeLDL_12_4_5
  · exact computeLDL_12_5_0
  · exact computeLDL_12_5_1
  · exact computeLDL_12_5_2
  · exact computeLDL_12_5_3
  · exact computeLDL_12_5_4
  · exact computeLDL_12_5_5

end Laughlin.Certificate

end OAI
