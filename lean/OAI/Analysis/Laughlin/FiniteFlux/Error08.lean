import OAI.Analysis.Laughlin.FiniteFlux.Row08
import OAI.Analysis.Laughlin.FiniteFlux.Row082
import OAI.Analysis.Laughlin.FiniteFlux.Row083
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem error_8_1_1 : Y 8 1 1 = (-67460768130800149252179/3355443200000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_1_1_0, yRow_8_1_1_1, yRow_8_1_1_2, yRow_8_1_1_3, yRow_8_1_1_4, yRow_8_1_1_5, yRow_8_1_1_6]
  norm_num

theorem error_8_1_3 : Y 8 1 3 = (-12646981826519267475639/1677721600000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_1_3_0, yRow_8_1_3_1, yRow_8_1_3_2, yRow_8_1_3_3, yRow_8_1_3_4, yRow_8_1_3_5, yRow_8_1_3_6]
  norm_num

theorem error_8_1_5 : Y 8 1 5 = (862312946559627131048937/6710886400000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_1_5_0, yRow_8_1_5_1, yRow_8_1_5_2, yRow_8_1_5_3, yRow_8_1_5_4, yRow_8_1_5_5, yRow_8_1_5_6]
  norm_num

theorem error_8_1_7 : Y 8 1 7 = (145152021796677708235047/3355443200000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_1_7_0, yRow_8_1_7_1, yRow_8_1_7_2, yRow_8_1_7_3, yRow_8_1_7_4, yRow_8_1_7_5, yRow_8_1_7_6]
  norm_num

theorem error_8_3_3 : Y 8 3 3 = (-227609666383850988434007/23488102400000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_3_3_0, yRow_8_3_3_1, yRow_8_3_3_2, yRow_8_3_3_3, yRow_8_3_3_4, yRow_8_3_3_5, yRow_8_3_3_6]
  norm_num

theorem error_8_3_5 : Y 8 3 5 = (-285716550006646092887421/23488102400000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_3_5_0, yRow_8_3_5_1, yRow_8_3_5_2, yRow_8_3_5_3, yRow_8_3_5_4, yRow_8_3_5_5, yRow_8_3_5_6]
  norm_num

theorem error_8_3_7 : Y 8 3 7 = (-140429284546716888797613/1677721600000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_3_7_0, yRow_8_3_7_1, yRow_8_3_7_2, yRow_8_3_7_3, yRow_8_3_7_4, yRow_8_3_7_5, yRow_8_3_7_6]
  norm_num

theorem error_8_5_5 : Y 8 5 5 = (1048952949137524188240279/46976204800000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_5_5_0, yRow_8_5_5_1, yRow_8_5_5_2, yRow_8_5_5_3, yRow_8_5_5_4, yRow_8_5_5_5, yRow_8_5_5_6]
  norm_num

theorem error_8_5_7 : Y 8 5 7 = (707573349496458024998847/3355443200000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_5_7_0, yRow_8_5_7_1, yRow_8_5_7_2, yRow_8_5_7_3, yRow_8_5_7_4, yRow_8_5_7_5, yRow_8_5_7_6]
  norm_num

theorem error_8_7_7 : Y 8 7 7 = (-2475302483264003426615343/1677721600000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_7_7_0, yRow_8_7_7_1, yRow_8_7_7_2, yRow_8_7_7_3, yRow_8_7_7_4, yRow_8_7_7_5, yRow_8_7_7_6]
  norm_num

theorem error_8_3_1 : Y 8 3 1 = (-12646981826519267475639/1677721600000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_1_3

theorem error_8_5_1 : Y 8 5 1 = (862312946559627131048937/6710886400000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_1_5

theorem error_8_5_3 : Y 8 5 3 = (-285716550006646092887421/23488102400000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_3_5

theorem error_8_7_1 : Y 8 7 1 = (145152021796677708235047/3355443200000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_1_7

theorem error_8_7_3 : Y 8 7 3 = (-140429284546716888797613/1677721600000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_3_7

theorem error_8_7_5 : Y 8 7 5 = (707573349496458024998847/3355443200000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_5_7
theorem error_8 : errorRational 8 =
    !![-67460768130800149252179/3355443200000000000000, -12646981826519267475639/1677721600000000000000, 862312946559627131048937/6710886400000000000000, 145152021796677708235047/3355443200000000000000;
      -12646981826519267475639/1677721600000000000000, -227609666383850988434007/23488102400000000000000, -285716550006646092887421/23488102400000000000000, -140429284546716888797613/1677721600000000000000;
      862312946559627131048937/6710886400000000000000, -285716550006646092887421/23488102400000000000000, 1048952949137524188240279/46976204800000000000000, 707573349496458024998847/3355443200000000000000;
      145152021796677708235047/3355443200000000000000, -140429284546716888797613/1677721600000000000000, 707573349496458024998847/3355443200000000000000, -2475302483264003426615343/1677721600000000000000] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact error_8_1_1
  · exact error_8_1_3
  · exact error_8_1_5
  · exact error_8_1_7
  · exact error_8_3_1
  · exact error_8_3_3
  · exact error_8_3_5
  · exact error_8_3_7
  · exact error_8_5_1
  · exact error_8_5_3
  · exact error_8_5_5
  · exact error_8_5_7
  · exact error_8_7_1
  · exact error_8_7_3
  · exact error_8_7_5
  · exact error_8_7_7

end Laughlin.Certificate

end OAI
