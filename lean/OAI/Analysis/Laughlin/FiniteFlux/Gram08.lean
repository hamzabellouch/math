import OAI.Analysis.Laughlin.FiniteFlux.Gram082
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem gram_8 : gramRational 8 =
  !![0, 0, 0, 0;
    0, 720, -720, 1260;
    0, -720, 720, -1260;
    0, 1260, -1260, 2205] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact gram_8_1_1
  · exact gram_8_1_3
  · exact gram_8_1_5
  · exact gram_8_1_7
  · exact (Z_symm 8 3 1).trans gram_8_1_3
  · exact gram_8_3_3
  · exact gram_8_3_5
  · exact gram_8_3_7
  · exact (Z_symm 8 5 1).trans gram_8_1_5
  · exact (Z_symm 8 5 3).trans gram_8_3_5
  · exact gram_8_5_5
  · exact gram_8_5_7
  · exact (Z_symm 8 7 1).trans gram_8_1_7
  · exact (Z_symm 8 7 3).trans gram_8_3_7
  · exact (Z_symm 8 7 5).trans gram_8_5_7
  · exact gram_8_7_7

end Laughlin.Certificate

end OAI
