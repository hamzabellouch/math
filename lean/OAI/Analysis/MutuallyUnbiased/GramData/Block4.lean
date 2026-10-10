import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check0
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check1
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check2
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check3
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check4
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check5
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check6
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check7
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check8
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check9
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check10
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check11
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check12
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check13
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check14
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check15
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check16
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check17
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check18
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check19
import OAI.Analysis.MutuallyUnbiased.GramData.Block4Check20

namespace OAI

namespace MUB6.Certificate.GramData.Block4

open Matrix
open scoped BigOperators

theorem pivots_pos : ∀ k : Fin 22, 0 < D k := by
  intro k
  fin_cases k
  · exact lt_trans (by norm_num) pivot_0
  · exact lt_trans (by norm_num) pivot_1
  · exact lt_trans (by norm_num) pivot_2
  · exact lt_trans (by norm_num) pivot_3
  · exact lt_trans (by norm_num) pivot_4
  · exact lt_trans (by norm_num) pivot_5
  · exact lt_trans (by norm_num) pivot_6
  · exact lt_trans (by norm_num) pivot_7
  · exact lt_trans (by norm_num) pivot_8
  · exact lt_trans (by norm_num) pivot_9
  · exact lt_trans (by norm_num) pivot_10
  · exact lt_trans (by norm_num) pivot_11
  · exact lt_trans (by norm_num) pivot_12
  · exact lt_trans (by norm_num) pivot_13
  · exact lt_trans (by norm_num) pivot_14
  · exact lt_trans (by norm_num) pivot_15
  · exact lt_trans (by norm_num) pivot_16
  · exact lt_trans (by norm_num) pivot_17
  · exact lt_trans (by norm_num) pivot_18
  · exact lt_trans (by norm_num) pivot_19
  · exact lt_trans (by norm_num) pivot_20
  · exact lt_trans (by norm_num) pivot_21

theorem gram : ∀ i j : Fin 22, Z i j =
    ∑ k, lowerUnit entries k i * D k * lowerUnit entries k j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact entry_0_0
  · exact entry_0_1
  · exact entry_0_2
  · exact entry_0_3
  · exact entry_0_4
  · exact entry_0_5
  · exact entry_0_6
  · exact entry_0_7
  · exact entry_0_8
  · exact entry_0_9
  · exact entry_0_10
  · exact entry_0_11
  · exact entry_0_12
  · exact entry_0_13
  · exact entry_0_14
  · exact entry_0_15
  · exact entry_0_16
  · exact entry_0_17
  · exact entry_0_18
  · exact entry_0_19
  · exact entry_0_20
  · exact entry_0_21
  · exact entry_1_0
  · exact entry_1_1
  · exact entry_1_2
  · exact entry_1_3
  · exact entry_1_4
  · exact entry_1_5
  · exact entry_1_6
  · exact entry_1_7
  · exact entry_1_8
  · exact entry_1_9
  · exact entry_1_10
  · exact entry_1_11
  · exact entry_1_12
  · exact entry_1_13
  · exact entry_1_14
  · exact entry_1_15
  · exact entry_1_16
  · exact entry_1_17
  · exact entry_1_18
  · exact entry_1_19
  · exact entry_1_20
  · exact entry_1_21
  · exact entry_2_0
  · exact entry_2_1
  · exact entry_2_2
  · exact entry_2_3
  · exact entry_2_4
  · exact entry_2_5
  · exact entry_2_6
  · exact entry_2_7
  · exact entry_2_8
  · exact entry_2_9
  · exact entry_2_10
  · exact entry_2_11
  · exact entry_2_12
  · exact entry_2_13
  · exact entry_2_14
  · exact entry_2_15
  · exact entry_2_16
  · exact entry_2_17
  · exact entry_2_18
  · exact entry_2_19
  · exact entry_2_20
  · exact entry_2_21
  · exact entry_3_0
  · exact entry_3_1
  · exact entry_3_2
  · exact entry_3_3
  · exact entry_3_4
  · exact entry_3_5
  · exact entry_3_6
  · exact entry_3_7
  · exact entry_3_8
  · exact entry_3_9
  · exact entry_3_10
  · exact entry_3_11
  · exact entry_3_12
  · exact entry_3_13
  · exact entry_3_14
  · exact entry_3_15
  · exact entry_3_16
  · exact entry_3_17
  · exact entry_3_18
  · exact entry_3_19
  · exact entry_3_20
  · exact entry_3_21
  · exact entry_4_0
  · exact entry_4_1
  · exact entry_4_2
  · exact entry_4_3
  · exact entry_4_4
  · exact entry_4_5
  · exact entry_4_6
  · exact entry_4_7
  · exact entry_4_8
  · exact entry_4_9
  · exact entry_4_10
  · exact entry_4_11
  · exact entry_4_12
  · exact entry_4_13
  · exact entry_4_14
  · exact entry_4_15
  · exact entry_4_16
  · exact entry_4_17
  · exact entry_4_18
  · exact entry_4_19
  · exact entry_4_20
  · exact entry_4_21
  · exact entry_5_0
  · exact entry_5_1
  · exact entry_5_2
  · exact entry_5_3
  · exact entry_5_4
  · exact entry_5_5
  · exact entry_5_6
  · exact entry_5_7
  · exact entry_5_8
  · exact entry_5_9
  · exact entry_5_10
  · exact entry_5_11
  · exact entry_5_12
  · exact entry_5_13
  · exact entry_5_14
  · exact entry_5_15
  · exact entry_5_16
  · exact entry_5_17
  · exact entry_5_18
  · exact entry_5_19
  · exact entry_5_20
  · exact entry_5_21
  · exact entry_6_0
  · exact entry_6_1
  · exact entry_6_2
  · exact entry_6_3
  · exact entry_6_4
  · exact entry_6_5
  · exact entry_6_6
  · exact entry_6_7
  · exact entry_6_8
  · exact entry_6_9
  · exact entry_6_10
  · exact entry_6_11
  · exact entry_6_12
  · exact entry_6_13
  · exact entry_6_14
  · exact entry_6_15
  · exact entry_6_16
  · exact entry_6_17
  · exact entry_6_18
  · exact entry_6_19
  · exact entry_6_20
  · exact entry_6_21
  · exact entry_7_0
  · exact entry_7_1
  · exact entry_7_2
  · exact entry_7_3
  · exact entry_7_4
  · exact entry_7_5
  · exact entry_7_6
  · exact entry_7_7
  · exact entry_7_8
  · exact entry_7_9
  · exact entry_7_10
  · exact entry_7_11
  · exact entry_7_12
  · exact entry_7_13
  · exact entry_7_14
  · exact entry_7_15
  · exact entry_7_16
  · exact entry_7_17
  · exact entry_7_18
  · exact entry_7_19
  · exact entry_7_20
  · exact entry_7_21
  · exact entry_8_0
  · exact entry_8_1
  · exact entry_8_2
  · exact entry_8_3
  · exact entry_8_4
  · exact entry_8_5
  · exact entry_8_6
  · exact entry_8_7
  · exact entry_8_8
  · exact entry_8_9
  · exact entry_8_10
  · exact entry_8_11
  · exact entry_8_12
  · exact entry_8_13
  · exact entry_8_14
  · exact entry_8_15
  · exact entry_8_16
  · exact entry_8_17
  · exact entry_8_18
  · exact entry_8_19
  · exact entry_8_20
  · exact entry_8_21
  · exact entry_9_0
  · exact entry_9_1
  · exact entry_9_2
  · exact entry_9_3
  · exact entry_9_4
  · exact entry_9_5
  · exact entry_9_6
  · exact entry_9_7
  · exact entry_9_8
  · exact entry_9_9
  · exact entry_9_10
  · exact entry_9_11
  · exact entry_9_12
  · exact entry_9_13
  · exact entry_9_14
  · exact entry_9_15
  · exact entry_9_16
  · exact entry_9_17
  · exact entry_9_18
  · exact entry_9_19
  · exact entry_9_20
  · exact entry_9_21
  · exact entry_10_0
  · exact entry_10_1
  · exact entry_10_2
  · exact entry_10_3
  · exact entry_10_4
  · exact entry_10_5
  · exact entry_10_6
  · exact entry_10_7
  · exact entry_10_8
  · exact entry_10_9
  · exact entry_10_10
  · exact entry_10_11
  · exact entry_10_12
  · exact entry_10_13
  · exact entry_10_14
  · exact entry_10_15
  · exact entry_10_16
  · exact entry_10_17
  · exact entry_10_18
  · exact entry_10_19
  · exact entry_10_20
  · exact entry_10_21
  · exact entry_11_0
  · exact entry_11_1
  · exact entry_11_2
  · exact entry_11_3
  · exact entry_11_4
  · exact entry_11_5
  · exact entry_11_6
  · exact entry_11_7
  · exact entry_11_8
  · exact entry_11_9
  · exact entry_11_10
  · exact entry_11_11
  · exact entry_11_12
  · exact entry_11_13
  · exact entry_11_14
  · exact entry_11_15
  · exact entry_11_16
  · exact entry_11_17
  · exact entry_11_18
  · exact entry_11_19
  · exact entry_11_20
  · exact entry_11_21
  · exact entry_12_0
  · exact entry_12_1
  · exact entry_12_2
  · exact entry_12_3
  · exact entry_12_4
  · exact entry_12_5
  · exact entry_12_6
  · exact entry_12_7
  · exact entry_12_8
  · exact entry_12_9
  · exact entry_12_10
  · exact entry_12_11
  · exact entry_12_12
  · exact entry_12_13
  · exact entry_12_14
  · exact entry_12_15
  · exact entry_12_16
  · exact entry_12_17
  · exact entry_12_18
  · exact entry_12_19
  · exact entry_12_20
  · exact entry_12_21
  · exact entry_13_0
  · exact entry_13_1
  · exact entry_13_2
  · exact entry_13_3
  · exact entry_13_4
  · exact entry_13_5
  · exact entry_13_6
  · exact entry_13_7
  · exact entry_13_8
  · exact entry_13_9
  · exact entry_13_10
  · exact entry_13_11
  · exact entry_13_12
  · exact entry_13_13
  · exact entry_13_14
  · exact entry_13_15
  · exact entry_13_16
  · exact entry_13_17
  · exact entry_13_18
  · exact entry_13_19
  · exact entry_13_20
  · exact entry_13_21
  · exact entry_14_0
  · exact entry_14_1
  · exact entry_14_2
  · exact entry_14_3
  · exact entry_14_4
  · exact entry_14_5
  · exact entry_14_6
  · exact entry_14_7
  · exact entry_14_8
  · exact entry_14_9
  · exact entry_14_10
  · exact entry_14_11
  · exact entry_14_12
  · exact entry_14_13
  · exact entry_14_14
  · exact entry_14_15
  · exact entry_14_16
  · exact entry_14_17
  · exact entry_14_18
  · exact entry_14_19
  · exact entry_14_20
  · exact entry_14_21
  · exact entry_15_0
  · exact entry_15_1
  · exact entry_15_2
  · exact entry_15_3
  · exact entry_15_4
  · exact entry_15_5
  · exact entry_15_6
  · exact entry_15_7
  · exact entry_15_8
  · exact entry_15_9
  · exact entry_15_10
  · exact entry_15_11
  · exact entry_15_12
  · exact entry_15_13
  · exact entry_15_14
  · exact entry_15_15
  · exact entry_15_16
  · exact entry_15_17
  · exact entry_15_18
  · exact entry_15_19
  · exact entry_15_20
  · exact entry_15_21
  · exact entry_16_0
  · exact entry_16_1
  · exact entry_16_2
  · exact entry_16_3
  · exact entry_16_4
  · exact entry_16_5
  · exact entry_16_6
  · exact entry_16_7
  · exact entry_16_8
  · exact entry_16_9
  · exact entry_16_10
  · exact entry_16_11
  · exact entry_16_12
  · exact entry_16_13
  · exact entry_16_14
  · exact entry_16_15
  · exact entry_16_16
  · exact entry_16_17
  · exact entry_16_18
  · exact entry_16_19
  · exact entry_16_20
  · exact entry_16_21
  · exact entry_17_0
  · exact entry_17_1
  · exact entry_17_2
  · exact entry_17_3
  · exact entry_17_4
  · exact entry_17_5
  · exact entry_17_6
  · exact entry_17_7
  · exact entry_17_8
  · exact entry_17_9
  · exact entry_17_10
  · exact entry_17_11
  · exact entry_17_12
  · exact entry_17_13
  · exact entry_17_14
  · exact entry_17_15
  · exact entry_17_16
  · exact entry_17_17
  · exact entry_17_18
  · exact entry_17_19
  · exact entry_17_20
  · exact entry_17_21
  · exact entry_18_0
  · exact entry_18_1
  · exact entry_18_2
  · exact entry_18_3
  · exact entry_18_4
  · exact entry_18_5
  · exact entry_18_6
  · exact entry_18_7
  · exact entry_18_8
  · exact entry_18_9
  · exact entry_18_10
  · exact entry_18_11
  · exact entry_18_12
  · exact entry_18_13
  · exact entry_18_14
  · exact entry_18_15
  · exact entry_18_16
  · exact entry_18_17
  · exact entry_18_18
  · exact entry_18_19
  · exact entry_18_20
  · exact entry_18_21
  · exact entry_19_0
  · exact entry_19_1
  · exact entry_19_2
  · exact entry_19_3
  · exact entry_19_4
  · exact entry_19_5
  · exact entry_19_6
  · exact entry_19_7
  · exact entry_19_8
  · exact entry_19_9
  · exact entry_19_10
  · exact entry_19_11
  · exact entry_19_12
  · exact entry_19_13
  · exact entry_19_14
  · exact entry_19_15
  · exact entry_19_16
  · exact entry_19_17
  · exact entry_19_18
  · exact entry_19_19
  · exact entry_19_20
  · exact entry_19_21
  · exact entry_20_0
  · exact entry_20_1
  · exact entry_20_2
  · exact entry_20_3
  · exact entry_20_4
  · exact entry_20_5
  · exact entry_20_6
  · exact entry_20_7
  · exact entry_20_8
  · exact entry_20_9
  · exact entry_20_10
  · exact entry_20_11
  · exact entry_20_12
  · exact entry_20_13
  · exact entry_20_14
  · exact entry_20_15
  · exact entry_20_16
  · exact entry_20_17
  · exact entry_20_18
  · exact entry_20_19
  · exact entry_20_20
  · exact entry_20_21
  · exact entry_21_0
  · exact entry_21_1
  · exact entry_21_2
  · exact entry_21_3
  · exact entry_21_4
  · exact entry_21_5
  · exact entry_21_6
  · exact entry_21_7
  · exact entry_21_8
  · exact entry_21_9
  · exact entry_21_10
  · exact entry_21_11
  · exact entry_21_12
  · exact entry_21_13
  · exact entry_21_14
  · exact entry_21_15
  · exact entry_21_16
  · exact entry_21_17
  · exact entry_21_18
  · exact entry_21_19
  · exact entry_21_20
  · exact entry_21_21

theorem positiveDefinite : (realMatrix Z).PosDef :=
  posDef_of_rational_gram Z entries D pivots_pos gram

end MUB6.Certificate.GramData.Block4

end OAI
