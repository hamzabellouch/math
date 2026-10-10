import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram11
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow11
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow112
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow113
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow114
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow115
import OAI.Analysis.Laughlin.FiniteFlux.Data11
import OAI.Analysis.Laughlin.FourBody.NumericBridge
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
theorem source_error_11_1_1 : Y 11 1 1 = (15310420495743050456853357/134217728000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 1 0 (by decide),
    source_yRow_eq_rowCompute 11 1 1 1 (by decide),
    source_yRow_eq_rowCompute 11 1 1 2 (by decide),
    source_yRow_eq_rowCompute 11 1 1 3 (by decide),
    source_yRow_eq_rowCompute 11 1 1 4 (by decide),
    source_yRow_eq_rowCompute 11 1 1 5 (by decide),
    source_yRow_eq_rowCompute 11 1 1 6 (by decide),
    computeRow_11_1_1_0, computeRow_11_1_1_1, computeRow_11_1_1_2, computeRow_11_1_1_3, computeRow_11_1_1_4, computeRow_11_1_1_5, computeRow_11_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_1_3 : Y 11 1 3 = (-21091981152473935416162441/335544320000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 3 0 (by decide),
    source_yRow_eq_rowCompute 11 1 3 1 (by decide),
    source_yRow_eq_rowCompute 11 1 3 2 (by decide),
    source_yRow_eq_rowCompute 11 1 3 3 (by decide),
    source_yRow_eq_rowCompute 11 1 3 4 (by decide),
    source_yRow_eq_rowCompute 11 1 3 5 (by decide),
    source_yRow_eq_rowCompute 11 1 3 6 (by decide),
    computeRow_11_1_3_0, computeRow_11_1_3_1, computeRow_11_1_3_2, computeRow_11_1_3_3, computeRow_11_1_3_4, computeRow_11_1_3_5, computeRow_11_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_1_5 : Y 11 1 5 = (1759644912412486678804947/134217728000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 5 0 (by decide),
    source_yRow_eq_rowCompute 11 1 5 1 (by decide),
    source_yRow_eq_rowCompute 11 1 5 2 (by decide),
    source_yRow_eq_rowCompute 11 1 5 3 (by decide),
    source_yRow_eq_rowCompute 11 1 5 4 (by decide),
    source_yRow_eq_rowCompute 11 1 5 5 (by decide),
    source_yRow_eq_rowCompute 11 1 5 6 (by decide),
    computeRow_11_1_5_0, computeRow_11_1_5_1, computeRow_11_1_5_2, computeRow_11_1_5_3, computeRow_11_1_5_4, computeRow_11_1_5_5, computeRow_11_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_1_7 : Y 11 1 7 = (-7117902998608090523107887/335544320000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 7 0 (by decide),
    source_yRow_eq_rowCompute 11 1 7 1 (by decide),
    source_yRow_eq_rowCompute 11 1 7 2 (by decide),
    source_yRow_eq_rowCompute 11 1 7 3 (by decide),
    source_yRow_eq_rowCompute 11 1 7 4 (by decide),
    source_yRow_eq_rowCompute 11 1 7 5 (by decide),
    source_yRow_eq_rowCompute 11 1 7 6 (by decide),
    computeRow_11_1_7_0, computeRow_11_1_7_1, computeRow_11_1_7_2, computeRow_11_1_7_3, computeRow_11_1_7_4, computeRow_11_1_7_5, computeRow_11_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_1_9 : Y 11 1 9 = (2050140304557578762479287/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 9 0 (by decide),
    source_yRow_eq_rowCompute 11 1 9 1 (by decide),
    source_yRow_eq_rowCompute 11 1 9 2 (by decide),
    source_yRow_eq_rowCompute 11 1 9 3 (by decide),
    source_yRow_eq_rowCompute 11 1 9 4 (by decide),
    source_yRow_eq_rowCompute 11 1 9 5 (by decide),
    source_yRow_eq_rowCompute 11 1 9 6 (by decide),
    computeRow_11_1_9_0, computeRow_11_1_9_1, computeRow_11_1_9_2, computeRow_11_1_9_3, computeRow_11_1_9_4, computeRow_11_1_9_5, computeRow_11_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_1_11 : Y 11 1 11 = (-3816671070411211699962099/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 11 0 (by decide),
    source_yRow_eq_rowCompute 11 1 11 1 (by decide),
    source_yRow_eq_rowCompute 11 1 11 2 (by decide),
    source_yRow_eq_rowCompute 11 1 11 3 (by decide),
    source_yRow_eq_rowCompute 11 1 11 4 (by decide),
    source_yRow_eq_rowCompute 11 1 11 5 (by decide),
    source_yRow_eq_rowCompute 11 1 11 6 (by decide),
    computeRow_11_1_11_0, computeRow_11_1_11_1, computeRow_11_1_11_2, computeRow_11_1_11_3, computeRow_11_1_11_4, computeRow_11_1_11_5, computeRow_11_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_3_3 : Y 11 3 3 = (3139824493398164330092707/167772160000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 3 3 0 (by decide),
    source_yRow_eq_rowCompute 11 3 3 1 (by decide),
    source_yRow_eq_rowCompute 11 3 3 2 (by decide),
    source_yRow_eq_rowCompute 11 3 3 3 (by decide),
    source_yRow_eq_rowCompute 11 3 3 4 (by decide),
    source_yRow_eq_rowCompute 11 3 3 5 (by decide),
    source_yRow_eq_rowCompute 11 3 3 6 (by decide),
    computeRow_11_3_3_0, computeRow_11_3_3_1, computeRow_11_3_3_2, computeRow_11_3_3_3, computeRow_11_3_3_4, computeRow_11_3_3_5, computeRow_11_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_3_5 : Y 11 3 5 = (-110846050581407277067047/13421772800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 3 5 0 (by decide),
    source_yRow_eq_rowCompute 11 3 5 1 (by decide),
    source_yRow_eq_rowCompute 11 3 5 2 (by decide),
    source_yRow_eq_rowCompute 11 3 5 3 (by decide),
    source_yRow_eq_rowCompute 11 3 5 4 (by decide),
    source_yRow_eq_rowCompute 11 3 5 5 (by decide),
    source_yRow_eq_rowCompute 11 3 5 6 (by decide),
    computeRow_11_3_5_0, computeRow_11_3_5_1, computeRow_11_3_5_2, computeRow_11_3_5_3, computeRow_11_3_5_4, computeRow_11_3_5_5, computeRow_11_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_3_7 : Y 11 3 7 = (-120000452149124136234801/167772160000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 3 7 0 (by decide),
    source_yRow_eq_rowCompute 11 3 7 1 (by decide),
    source_yRow_eq_rowCompute 11 3 7 2 (by decide),
    source_yRow_eq_rowCompute 11 3 7 3 (by decide),
    source_yRow_eq_rowCompute 11 3 7 4 (by decide),
    source_yRow_eq_rowCompute 11 3 7 5 (by decide),
    source_yRow_eq_rowCompute 11 3 7 6 (by decide),
    computeRow_11_3_7_0, computeRow_11_3_7_1, computeRow_11_3_7_2, computeRow_11_3_7_3, computeRow_11_3_7_4, computeRow_11_3_7_5, computeRow_11_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_3_9 : Y 11 3 9 = (-804905973848069092119267/41943040000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 3 9 0 (by decide),
    source_yRow_eq_rowCompute 11 3 9 1 (by decide),
    source_yRow_eq_rowCompute 11 3 9 2 (by decide),
    source_yRow_eq_rowCompute 11 3 9 3 (by decide),
    source_yRow_eq_rowCompute 11 3 9 4 (by decide),
    source_yRow_eq_rowCompute 11 3 9 5 (by decide),
    source_yRow_eq_rowCompute 11 3 9 6 (by decide),
    computeRow_11_3_9_0, computeRow_11_3_9_1, computeRow_11_3_9_2, computeRow_11_3_9_3, computeRow_11_3_9_4, computeRow_11_3_9_5, computeRow_11_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_3_11 : Y 11 3 11 = (-488664944191263381981813/20971520000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 3 11 0 (by decide),
    source_yRow_eq_rowCompute 11 3 11 1 (by decide),
    source_yRow_eq_rowCompute 11 3 11 2 (by decide),
    source_yRow_eq_rowCompute 11 3 11 3 (by decide),
    source_yRow_eq_rowCompute 11 3 11 4 (by decide),
    source_yRow_eq_rowCompute 11 3 11 5 (by decide),
    source_yRow_eq_rowCompute 11 3 11 6 (by decide),
    computeRow_11_3_11_0, computeRow_11_3_11_1, computeRow_11_3_11_2, computeRow_11_3_11_3, computeRow_11_3_11_4, computeRow_11_3_11_5, computeRow_11_3_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_5_5 : Y 11 5 5 = (186561496958160530399967/134217728000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 5 5 0 (by decide),
    source_yRow_eq_rowCompute 11 5 5 1 (by decide),
    source_yRow_eq_rowCompute 11 5 5 2 (by decide),
    source_yRow_eq_rowCompute 11 5 5 3 (by decide),
    source_yRow_eq_rowCompute 11 5 5 4 (by decide),
    source_yRow_eq_rowCompute 11 5 5 5 (by decide),
    source_yRow_eq_rowCompute 11 5 5 6 (by decide),
    computeRow_11_5_5_0, computeRow_11_5_5_1, computeRow_11_5_5_2, computeRow_11_5_5_3, computeRow_11_5_5_4, computeRow_11_5_5_5, computeRow_11_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_5_7 : Y 11 5 7 = (-132022995280028243088831/67108864000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 5 7 0 (by decide),
    source_yRow_eq_rowCompute 11 5 7 1 (by decide),
    source_yRow_eq_rowCompute 11 5 7 2 (by decide),
    source_yRow_eq_rowCompute 11 5 7 3 (by decide),
    source_yRow_eq_rowCompute 11 5 7 4 (by decide),
    source_yRow_eq_rowCompute 11 5 7 5 (by decide),
    source_yRow_eq_rowCompute 11 5 7 6 (by decide),
    computeRow_11_5_7_0, computeRow_11_5_7_1, computeRow_11_5_7_2, computeRow_11_5_7_3, computeRow_11_5_7_4, computeRow_11_5_7_5, computeRow_11_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_5_9 : Y 11 5 9 = (39011604836809336804287/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 5 9 0 (by decide),
    source_yRow_eq_rowCompute 11 5 9 1 (by decide),
    source_yRow_eq_rowCompute 11 5 9 2 (by decide),
    source_yRow_eq_rowCompute 11 5 9 3 (by decide),
    source_yRow_eq_rowCompute 11 5 9 4 (by decide),
    source_yRow_eq_rowCompute 11 5 9 5 (by decide),
    source_yRow_eq_rowCompute 11 5 9 6 (by decide),
    computeRow_11_5_9_0, computeRow_11_5_9_1, computeRow_11_5_9_2, computeRow_11_5_9_3, computeRow_11_5_9_4, computeRow_11_5_9_5, computeRow_11_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_5_11 : Y 11 5 11 = (-536635508982633719381547/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 5 11 0 (by decide),
    source_yRow_eq_rowCompute 11 5 11 1 (by decide),
    source_yRow_eq_rowCompute 11 5 11 2 (by decide),
    source_yRow_eq_rowCompute 11 5 11 3 (by decide),
    source_yRow_eq_rowCompute 11 5 11 4 (by decide),
    source_yRow_eq_rowCompute 11 5 11 5 (by decide),
    source_yRow_eq_rowCompute 11 5 11 6 (by decide),
    computeRow_11_5_11_0, computeRow_11_5_11_1, computeRow_11_5_11_2, computeRow_11_5_11_3, computeRow_11_5_11_4, computeRow_11_5_11_5, computeRow_11_5_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_7_7 : Y 11 7 7 = (53081184869685889157043/167772160000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 7 7 0 (by decide),
    source_yRow_eq_rowCompute 11 7 7 1 (by decide),
    source_yRow_eq_rowCompute 11 7 7 2 (by decide),
    source_yRow_eq_rowCompute 11 7 7 3 (by decide),
    source_yRow_eq_rowCompute 11 7 7 4 (by decide),
    source_yRow_eq_rowCompute 11 7 7 5 (by decide),
    source_yRow_eq_rowCompute 11 7 7 6 (by decide),
    computeRow_11_7_7_0, computeRow_11_7_7_1, computeRow_11_7_7_2, computeRow_11_7_7_3, computeRow_11_7_7_4, computeRow_11_7_7_5, computeRow_11_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_7_9 : Y 11 7 9 = (581826960578730870868149/41943040000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 7 9 0 (by decide),
    source_yRow_eq_rowCompute 11 7 9 1 (by decide),
    source_yRow_eq_rowCompute 11 7 9 2 (by decide),
    source_yRow_eq_rowCompute 11 7 9 3 (by decide),
    source_yRow_eq_rowCompute 11 7 9 4 (by decide),
    source_yRow_eq_rowCompute 11 7 9 5 (by decide),
    source_yRow_eq_rowCompute 11 7 9 6 (by decide),
    computeRow_11_7_9_0, computeRow_11_7_9_1, computeRow_11_7_9_2, computeRow_11_7_9_3, computeRow_11_7_9_4, computeRow_11_7_9_5, computeRow_11_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_7_11 : Y 11 7 11 = (48169578758531066711919/20971520000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 7 11 0 (by decide),
    source_yRow_eq_rowCompute 11 7 11 1 (by decide),
    source_yRow_eq_rowCompute 11 7 11 2 (by decide),
    source_yRow_eq_rowCompute 11 7 11 3 (by decide),
    source_yRow_eq_rowCompute 11 7 11 4 (by decide),
    source_yRow_eq_rowCompute 11 7 11 5 (by decide),
    source_yRow_eq_rowCompute 11 7 11 6 (by decide),
    computeRow_11_7_11_0, computeRow_11_7_11_1, computeRow_11_7_11_2, computeRow_11_7_11_3, computeRow_11_7_11_4, computeRow_11_7_11_5, computeRow_11_7_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_9_9 : Y 11 9 9 = (-985704999590345844614157/10485760000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 9 9 0 (by decide),
    source_yRow_eq_rowCompute 11 9 9 1 (by decide),
    source_yRow_eq_rowCompute 11 9 9 2 (by decide),
    source_yRow_eq_rowCompute 11 9 9 3 (by decide),
    source_yRow_eq_rowCompute 11 9 9 4 (by decide),
    source_yRow_eq_rowCompute 11 9 9 5 (by decide),
    source_yRow_eq_rowCompute 11 9 9 6 (by decide),
    computeRow_11_9_9_0, computeRow_11_9_9_1, computeRow_11_9_9_2, computeRow_11_9_9_3, computeRow_11_9_9_4, computeRow_11_9_9_5, computeRow_11_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_9_11 : Y 11 9 11 = (390621018140645815377261/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 9 11 0 (by decide),
    source_yRow_eq_rowCompute 11 9 11 1 (by decide),
    source_yRow_eq_rowCompute 11 9 11 2 (by decide),
    source_yRow_eq_rowCompute 11 9 11 3 (by decide),
    source_yRow_eq_rowCompute 11 9 11 4 (by decide),
    source_yRow_eq_rowCompute 11 9 11 5 (by decide),
    source_yRow_eq_rowCompute 11 9 11 6 (by decide),
    computeRow_11_9_11_0, computeRow_11_9_11_1, computeRow_11_9_11_2, computeRow_11_9_11_3, computeRow_11_9_11_4, computeRow_11_9_11_5, computeRow_11_9_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_11_11 : Y 11 11 11 = (-7434351034101698173344801/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 11 11 0 (by decide),
    source_yRow_eq_rowCompute 11 11 11 1 (by decide),
    source_yRow_eq_rowCompute 11 11 11 2 (by decide),
    source_yRow_eq_rowCompute 11 11 11 3 (by decide),
    source_yRow_eq_rowCompute 11 11 11 4 (by decide),
    source_yRow_eq_rowCompute 11 11 11 5 (by decide),
    source_yRow_eq_rowCompute 11 11 11 6 (by decide),
    computeRow_11_11_11_0, computeRow_11_11_11_1, computeRow_11_11_11_2, computeRow_11_11_11_3, computeRow_11_11_11_4, computeRow_11_11_11_5, computeRow_11_11_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_11_1_1 : Z 11 1 1 = (7257600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_1

theorem source_gram_11_1_3 : Z 11 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_3

theorem source_gram_11_1_5 : Z 11 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_5

theorem source_gram_11_1_7 : Z 11 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_7

theorem source_gram_11_1_9 : Z 11 1 9 = (-453600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_9

theorem source_gram_11_1_11 : Z 11 1 11 = (9979200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_11

theorem source_gram_11_3_3 : Z 11 3 3 = (241920 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_3

theorem source_gram_11_3_5 : Z 11 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_5

theorem source_gram_11_3_7 : Z 11 3 7 = (-60480 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_7

theorem source_gram_11_3_9 : Z 11 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_9

theorem source_gram_11_3_11 : Z 11 3 11 = (2494800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_11

theorem source_gram_11_5_5 : Z 11 5 5 = (54000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_5

theorem source_gram_11_5_7 : Z 11 5 7 = (-75600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_7

theorem source_gram_11_5_9 : Z 11 5 9 = (113400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_9

theorem source_gram_11_5_11 : Z 11 5 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_11

theorem source_gram_11_7_7 : Z 11 7 7 = (120960 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_7_7

theorem source_gram_11_7_9 : Z 11 7 9 = (-158760 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_7_9

theorem source_gram_11_7_11 : Z 11 7 11 = (-623700 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_7_11

theorem source_gram_11_9_9 : Z 11 9 9 = (266490 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_9_9

theorem source_gram_11_9_11 : Z 11 9 11 = (-623700 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_9_11

theorem source_gram_11_11_11 : Z 11 11 11 = (39449025 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_11_11

theorem source_error_11_3_1 : Y 11 3 1 = (-21091981152473935416162441/335544320000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_1_3

theorem source_gram_11_3_1 : Z 11 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_3

theorem source_error_11_5_1 : Y 11 5 1 = (1759644912412486678804947/134217728000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_1_5

theorem source_gram_11_5_1 : Z 11 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_5

theorem source_error_11_5_3 : Y 11 5 3 = (-110846050581407277067047/13421772800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_3_5

theorem source_gram_11_5_3 : Z 11 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_5

theorem source_error_11_7_1 : Y 11 7 1 = (-7117902998608090523107887/335544320000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_1_7

theorem source_gram_11_7_1 : Z 11 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_7

theorem source_error_11_7_3 : Y 11 7 3 = (-120000452149124136234801/167772160000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_3_7

theorem source_gram_11_7_3 : Z 11 7 3 = (-60480 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_7

theorem source_error_11_7_5 : Y 11 7 5 = (-132022995280028243088831/67108864000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_5_7

theorem source_gram_11_7_5 : Z 11 7 5 = (-75600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_5_7

theorem source_error_11_9_1 : Y 11 9 1 = (2050140304557578762479287/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_1_9

theorem source_gram_11_9_1 : Z 11 9 1 = (-453600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_9

theorem source_error_11_9_3 : Y 11 9 3 = (-804905973848069092119267/41943040000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_3_9

theorem source_gram_11_9_3 : Z 11 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_9

theorem source_error_11_9_5 : Y 11 9 5 = (39011604836809336804287/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_5_9

theorem source_gram_11_9_5 : Z 11 9 5 = (113400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_5_9

theorem source_error_11_9_7 : Y 11 9 7 = (581826960578730870868149/41943040000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_7_9

theorem source_gram_11_9_7 : Z 11 9 7 = (-158760 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_7_9

theorem source_error_11_11_1 : Y 11 11 1 = (-3816671070411211699962099/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_1_11

theorem source_gram_11_11_1 : Z 11 11 1 = (9979200 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_11

theorem source_error_11_11_3 : Y 11 11 3 = (-488664944191263381981813/20971520000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_3_11

theorem source_gram_11_11_3 : Z 11 11 3 = (2494800 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_11

theorem source_error_11_11_5 : Y 11 11 5 = (-536635508982633719381547/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_5_11

theorem source_gram_11_11_5 : Z 11 11 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_5_11

theorem source_error_11_11_7 : Y 11 11 7 = (48169578758531066711919/20971520000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_7_11

theorem source_gram_11_11_7 : Z 11 11 7 = (-623700 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_7_11

theorem source_error_11_11_9 : Y 11 11 9 = (390621018140645815377261/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_9_11

theorem source_gram_11_11_9 : Z 11 11 9 = (-623700 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_9_11

theorem error_11 : errorRational 11 = candidateY_11 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_11_1_1
  · exact source_error_11_1_3
  · exact source_error_11_1_5
  · exact source_error_11_1_7
  · exact source_error_11_1_9
  · exact source_error_11_1_11
  · exact source_error_11_3_1
  · exact source_error_11_3_3
  · exact source_error_11_3_5
  · exact source_error_11_3_7
  · exact source_error_11_3_9
  · exact source_error_11_3_11
  · exact source_error_11_5_1
  · exact source_error_11_5_3
  · exact source_error_11_5_5
  · exact source_error_11_5_7
  · exact source_error_11_5_9
  · exact source_error_11_5_11
  · exact source_error_11_7_1
  · exact source_error_11_7_3
  · exact source_error_11_7_5
  · exact source_error_11_7_7
  · exact source_error_11_7_9
  · exact source_error_11_7_11
  · exact source_error_11_9_1
  · exact source_error_11_9_3
  · exact source_error_11_9_5
  · exact source_error_11_9_7
  · exact source_error_11_9_9
  · exact source_error_11_9_11
  · exact source_error_11_11_1
  · exact source_error_11_11_3
  · exact source_error_11_11_5
  · exact source_error_11_11_7
  · exact source_error_11_11_9
  · exact source_error_11_11_11

theorem gram_11 : gramRational 11 = candidateZ_11 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_11_1_1
  · exact source_gram_11_1_3
  · exact source_gram_11_1_5
  · exact source_gram_11_1_7
  · exact source_gram_11_1_9
  · exact source_gram_11_1_11
  · exact source_gram_11_3_1
  · exact source_gram_11_3_3
  · exact source_gram_11_3_5
  · exact source_gram_11_3_7
  · exact source_gram_11_3_9
  · exact source_gram_11_3_11
  · exact source_gram_11_5_1
  · exact source_gram_11_5_3
  · exact source_gram_11_5_5
  · exact source_gram_11_5_7
  · exact source_gram_11_5_9
  · exact source_gram_11_5_11
  · exact source_gram_11_7_1
  · exact source_gram_11_7_3
  · exact source_gram_11_7_5
  · exact source_gram_11_7_7
  · exact source_gram_11_7_9
  · exact source_gram_11_7_11
  · exact source_gram_11_9_1
  · exact source_gram_11_9_3
  · exact source_gram_11_9_5
  · exact source_gram_11_9_7
  · exact source_gram_11_9_9
  · exact source_gram_11_9_11
  · exact source_gram_11_11_1
  · exact source_gram_11_11_3
  · exact source_gram_11_11_5
  · exact source_gram_11_11_7
  · exact source_gram_11_11_9
  · exact source_gram_11_11_11

end Laughlin.Certificate

end OAI
