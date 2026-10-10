import OAI.Analysis.Laughlin.FiniteFlux.Row05
import OAI.Analysis.Laughlin.FiniteFlux.Row052

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem error_five_11 : Y 5 1 1 = (-131383098735399323103/3355443200000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_1_1_0, yRow_5_1_1_1, yRow_5_1_1_2, yRow_5_1_1_3, yRow_5_1_1_4, yRow_5_1_1_5, yRow_5_1_1_6]
  norm_num

theorem error_five_13 : Y 5 1 3 = (-150940901726840366220441/187904819200000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_1_3_0, yRow_5_1_3_1, yRow_5_1_3_2, yRow_5_1_3_3, yRow_5_1_3_4, yRow_5_1_3_5, yRow_5_1_3_6]
  norm_num

theorem error_five_15 : Y 5 1 5 = (-68371964800993572891617/375809638400000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_1_5_0, yRow_5_1_5_1, yRow_5_1_5_2, yRow_5_1_5_3, yRow_5_1_5_4, yRow_5_1_5_5, yRow_5_1_5_6]
  norm_num

theorem error_five_31 : Y 5 3 1 = (-150940901726840366220441/187904819200000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_3_1_0, yRow_5_3_1_1, yRow_5_3_1_2, yRow_5_3_1_3, yRow_5_3_1_4, yRow_5_3_1_5, yRow_5_3_1_6]
  norm_num

theorem error_five_33 : Y 5 3 3 = (-157876378364069020620837/187904819200000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_3_3_0, yRow_5_3_3_1, yRow_5_3_3_2, yRow_5_3_3_3, yRow_5_3_3_4, yRow_5_3_3_5, yRow_5_3_3_6]
  norm_num

theorem error_five_35 : Y 5 3 5 = (-957095703323798289717/367001600000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_3_5_0, yRow_5_3_5_1, yRow_5_3_5_2, yRow_5_3_5_3, yRow_5_3_5_4, yRow_5_3_5_5, yRow_5_3_5_6]
  norm_num

theorem error_five_51 : Y 5 5 1 = (-68371964800993572891617/375809638400000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_5_1_0, yRow_5_5_1_1, yRow_5_5_1_2, yRow_5_5_1_3, yRow_5_5_1_4, yRow_5_5_1_5, yRow_5_5_1_6]
  norm_num

theorem error_five_53 : Y 5 5 3 = (-957095703323798289717/367001600000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_5_3_0, yRow_5_5_3_1, yRow_5_5_3_2, yRow_5_5_3_3, yRow_5_5_3_4, yRow_5_5_3_5, yRow_5_5_3_6]
  norm_num

theorem error_five_55 : Y 5 5 5 = (-6732043280507644550567857/375809638400000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_5_5_0, yRow_5_5_5_1, yRow_5_5_5_2, yRow_5_5_5_3, yRow_5_5_5_4, yRow_5_5_5_5, yRow_5_5_5_6]
  norm_num
theorem error_five : errorRational 5 =
    !![-131383098735399323103/3355443200000000000000, -150940901726840366220441/187904819200000000000000, -68371964800993572891617/375809638400000000000000;
      -150940901726840366220441/187904819200000000000000, -157876378364069020620837/187904819200000000000000, -957095703323798289717/367001600000000000000;
      -68371964800993572891617/375809638400000000000000, -957095703323798289717/367001600000000000000, -6732043280507644550567857/375809638400000000000000] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact error_five_11
  · exact error_five_13
  · exact error_five_15
  · exact error_five_31
  · exact error_five_33
  · exact error_five_35
  · exact error_five_51
  · exact error_five_53
  · exact error_five_55

end Laughlin.Certificate

end OAI
