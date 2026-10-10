import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram10
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow10
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow102
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow103
import OAI.Analysis.Laughlin.FiniteFlux.Data10
import OAI.Analysis.Laughlin.FourBody.NumericBridge
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
theorem source_error_10_1_1 : Y 10 1 1 = (3252603773208384966897801/134217728000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 1 1 0 (by decide),
    source_yRow_eq_rowCompute 10 1 1 1 (by decide),
    source_yRow_eq_rowCompute 10 1 1 2 (by decide),
    source_yRow_eq_rowCompute 10 1 1 3 (by decide),
    source_yRow_eq_rowCompute 10 1 1 4 (by decide),
    source_yRow_eq_rowCompute 10 1 1 5 (by decide),
    source_yRow_eq_rowCompute 10 1 1 6 (by decide),
    computeRow_10_1_1_0, computeRow_10_1_1_1, computeRow_10_1_1_2, computeRow_10_1_1_3, computeRow_10_1_1_4, computeRow_10_1_1_5, computeRow_10_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_1_3 : Y 10 1 3 = (-1219963203744052188572919/167772160000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 1 3 0 (by decide),
    source_yRow_eq_rowCompute 10 1 3 1 (by decide),
    source_yRow_eq_rowCompute 10 1 3 2 (by decide),
    source_yRow_eq_rowCompute 10 1 3 3 (by decide),
    source_yRow_eq_rowCompute 10 1 3 4 (by decide),
    source_yRow_eq_rowCompute 10 1 3 5 (by decide),
    source_yRow_eq_rowCompute 10 1 3 6 (by decide),
    computeRow_10_1_3_0, computeRow_10_1_3_1, computeRow_10_1_3_2, computeRow_10_1_3_3, computeRow_10_1_3_4, computeRow_10_1_3_5, computeRow_10_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_1_5 : Y 10 1 5 = (1233781148459940320874483/134217728000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 1 5 0 (by decide),
    source_yRow_eq_rowCompute 10 1 5 1 (by decide),
    source_yRow_eq_rowCompute 10 1 5 2 (by decide),
    source_yRow_eq_rowCompute 10 1 5 3 (by decide),
    source_yRow_eq_rowCompute 10 1 5 4 (by decide),
    source_yRow_eq_rowCompute 10 1 5 5 (by decide),
    source_yRow_eq_rowCompute 10 1 5 6 (by decide),
    computeRow_10_1_5_0, computeRow_10_1_5_1, computeRow_10_1_5_2, computeRow_10_1_5_3, computeRow_10_1_5_4, computeRow_10_1_5_5, computeRow_10_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_1_7 : Y 10 1 7 = (-4673143458544379455879083/335544320000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 1 7 0 (by decide),
    source_yRow_eq_rowCompute 10 1 7 1 (by decide),
    source_yRow_eq_rowCompute 10 1 7 2 (by decide),
    source_yRow_eq_rowCompute 10 1 7 3 (by decide),
    source_yRow_eq_rowCompute 10 1 7 4 (by decide),
    source_yRow_eq_rowCompute 10 1 7 5 (by decide),
    source_yRow_eq_rowCompute 10 1 7 6 (by decide),
    computeRow_10_1_7_0, computeRow_10_1_7_1, computeRow_10_1_7_2, computeRow_10_1_7_3, computeRow_10_1_7_4, computeRow_10_1_7_5, computeRow_10_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_1_9 : Y 10 1 9 = (2012606963507139814961019/83886080000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 1 9 0 (by decide),
    source_yRow_eq_rowCompute 10 1 9 1 (by decide),
    source_yRow_eq_rowCompute 10 1 9 2 (by decide),
    source_yRow_eq_rowCompute 10 1 9 3 (by decide),
    source_yRow_eq_rowCompute 10 1 9 4 (by decide),
    source_yRow_eq_rowCompute 10 1 9 5 (by decide),
    source_yRow_eq_rowCompute 10 1 9 6 (by decide),
    computeRow_10_1_9_0, computeRow_10_1_9_1, computeRow_10_1_9_2, computeRow_10_1_9_3, computeRow_10_1_9_4, computeRow_10_1_9_5, computeRow_10_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_3_3 : Y 10 3 3 = (23917264894764854794377/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 3 3 0 (by decide),
    source_yRow_eq_rowCompute 10 3 3 1 (by decide),
    source_yRow_eq_rowCompute 10 3 3 2 (by decide),
    source_yRow_eq_rowCompute 10 3 3 3 (by decide),
    source_yRow_eq_rowCompute 10 3 3 4 (by decide),
    source_yRow_eq_rowCompute 10 3 3 5 (by decide),
    source_yRow_eq_rowCompute 10 3 3 6 (by decide),
    computeRow_10_3_3_0, computeRow_10_3_3_1, computeRow_10_3_3_2, computeRow_10_3_3_3, computeRow_10_3_3_4, computeRow_10_3_3_5, computeRow_10_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_3_5 : Y 10 3 5 = (-13854999171694482915831/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 3 5 0 (by decide),
    source_yRow_eq_rowCompute 10 3 5 1 (by decide),
    source_yRow_eq_rowCompute 10 3 5 2 (by decide),
    source_yRow_eq_rowCompute 10 3 5 3 (by decide),
    source_yRow_eq_rowCompute 10 3 5 4 (by decide),
    source_yRow_eq_rowCompute 10 3 5 5 (by decide),
    source_yRow_eq_rowCompute 10 3 5 6 (by decide),
    computeRow_10_3_5_0, computeRow_10_3_5_1, computeRow_10_3_5_2, computeRow_10_3_5_3, computeRow_10_3_5_4, computeRow_10_3_5_5, computeRow_10_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_3_7 : Y 10 3 7 = (57805337880323795919969/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 3 7 0 (by decide),
    source_yRow_eq_rowCompute 10 3 7 1 (by decide),
    source_yRow_eq_rowCompute 10 3 7 2 (by decide),
    source_yRow_eq_rowCompute 10 3 7 3 (by decide),
    source_yRow_eq_rowCompute 10 3 7 4 (by decide),
    source_yRow_eq_rowCompute 10 3 7 5 (by decide),
    source_yRow_eq_rowCompute 10 3 7 6 (by decide),
    computeRow_10_3_7_0, computeRow_10_3_7_1, computeRow_10_3_7_2, computeRow_10_3_7_3, computeRow_10_3_7_4, computeRow_10_3_7_5, computeRow_10_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_3_9 : Y 10 3 9 = (-52562004903703102850037/5242880000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 3 9 0 (by decide),
    source_yRow_eq_rowCompute 10 3 9 1 (by decide),
    source_yRow_eq_rowCompute 10 3 9 2 (by decide),
    source_yRow_eq_rowCompute 10 3 9 3 (by decide),
    source_yRow_eq_rowCompute 10 3 9 4 (by decide),
    source_yRow_eq_rowCompute 10 3 9 5 (by decide),
    source_yRow_eq_rowCompute 10 3 9 6 (by decide),
    computeRow_10_3_9_0, computeRow_10_3_9_1, computeRow_10_3_9_2, computeRow_10_3_9_3, computeRow_10_3_9_4, computeRow_10_3_9_5, computeRow_10_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_5_5 : Y 10 5 5 = (2285267576183515842978393/939524096000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 5 5 0 (by decide),
    source_yRow_eq_rowCompute 10 5 5 1 (by decide),
    source_yRow_eq_rowCompute 10 5 5 2 (by decide),
    source_yRow_eq_rowCompute 10 5 5 3 (by decide),
    source_yRow_eq_rowCompute 10 5 5 4 (by decide),
    source_yRow_eq_rowCompute 10 5 5 5 (by decide),
    source_yRow_eq_rowCompute 10 5 5 6 (by decide),
    computeRow_10_5_5_0, computeRow_10_5_5_1, computeRow_10_5_5_2, computeRow_10_5_5_3, computeRow_10_5_5_4, computeRow_10_5_5_5, computeRow_10_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_5_7 : Y 10 5 7 = (-121198635809384297528619/67108864000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 5 7 0 (by decide),
    source_yRow_eq_rowCompute 10 5 7 1 (by decide),
    source_yRow_eq_rowCompute 10 5 7 2 (by decide),
    source_yRow_eq_rowCompute 10 5 7 3 (by decide),
    source_yRow_eq_rowCompute 10 5 7 4 (by decide),
    source_yRow_eq_rowCompute 10 5 7 5 (by decide),
    source_yRow_eq_rowCompute 10 5 7 6 (by decide),
    computeRow_10_5_7_0, computeRow_10_5_7_1, computeRow_10_5_7_2, computeRow_10_5_7_3, computeRow_10_5_7_4, computeRow_10_5_7_5, computeRow_10_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_5_9 : Y 10 5 9 = (127922353790121014632767/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 5 9 0 (by decide),
    source_yRow_eq_rowCompute 10 5 9 1 (by decide),
    source_yRow_eq_rowCompute 10 5 9 2 (by decide),
    source_yRow_eq_rowCompute 10 5 9 3 (by decide),
    source_yRow_eq_rowCompute 10 5 9 4 (by decide),
    source_yRow_eq_rowCompute 10 5 9 5 (by decide),
    source_yRow_eq_rowCompute 10 5 9 6 (by decide),
    computeRow_10_5_9_0, computeRow_10_5_9_1, computeRow_10_5_9_2, computeRow_10_5_9_3, computeRow_10_5_9_4, computeRow_10_5_9_5, computeRow_10_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_7_7 : Y 10 7 7 = (51194502011873480782923/167772160000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 7 7 0 (by decide),
    source_yRow_eq_rowCompute 10 7 7 1 (by decide),
    source_yRow_eq_rowCompute 10 7 7 2 (by decide),
    source_yRow_eq_rowCompute 10 7 7 3 (by decide),
    source_yRow_eq_rowCompute 10 7 7 4 (by decide),
    source_yRow_eq_rowCompute 10 7 7 5 (by decide),
    source_yRow_eq_rowCompute 10 7 7 6 (by decide),
    computeRow_10_7_7_0, computeRow_10_7_7_1, computeRow_10_7_7_2, computeRow_10_7_7_3, computeRow_10_7_7_4, computeRow_10_7_7_5, computeRow_10_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_7_9 : Y 10 7 9 = (10203611212469228878953/41943040000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 7 9 0 (by decide),
    source_yRow_eq_rowCompute 10 7 9 1 (by decide),
    source_yRow_eq_rowCompute 10 7 9 2 (by decide),
    source_yRow_eq_rowCompute 10 7 9 3 (by decide),
    source_yRow_eq_rowCompute 10 7 9 4 (by decide),
    source_yRow_eq_rowCompute 10 7 9 5 (by decide),
    source_yRow_eq_rowCompute 10 7 9 6 (by decide),
    computeRow_10_7_9_0, computeRow_10_7_9_1, computeRow_10_7_9_2, computeRow_10_7_9_3, computeRow_10_7_9_4, computeRow_10_7_9_5, computeRow_10_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_9_9 : Y 10 9 9 = (-990036939147267786688413/10485760000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 9 9 0 (by decide),
    source_yRow_eq_rowCompute 10 9 9 1 (by decide),
    source_yRow_eq_rowCompute 10 9 9 2 (by decide),
    source_yRow_eq_rowCompute 10 9 9 3 (by decide),
    source_yRow_eq_rowCompute 10 9 9 4 (by decide),
    source_yRow_eq_rowCompute 10 9 9 5 (by decide),
    source_yRow_eq_rowCompute 10 9 9 6 (by decide),
    computeRow_10_9_9_0, computeRow_10_9_9_1, computeRow_10_9_9_2, computeRow_10_9_9_3, computeRow_10_9_9_4, computeRow_10_9_9_5, computeRow_10_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_10_1_1 : Z 10 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_1

theorem source_gram_10_1_3 : Z 10 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_3

theorem source_gram_10_1_5 : Z 10 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_5

theorem source_gram_10_1_7 : Z 10 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_7

theorem source_gram_10_1_9 : Z 10 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_9

theorem source_gram_10_3_3 : Z 10 3 3 = (30240 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_3

theorem source_gram_10_3_5 : Z 10 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_5

theorem source_gram_10_3_7 : Z 10 3 7 = (-22680 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_7

theorem source_gram_10_3_9 : Z 10 3 9 = (90720 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_9

theorem source_gram_10_5_5 : Z 10 5 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_5_5

theorem source_gram_10_5_7 : Z 10 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_5_7

theorem source_gram_10_5_9 : Z 10 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_5_9

theorem source_gram_10_7_7 : Z 10 7 7 = (17010 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_7_7

theorem source_gram_10_7_9 : Z 10 7 9 = (-68040 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_7_9

theorem source_gram_10_9_9 : Z 10 9 9 = (272160 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_9_9

theorem source_error_10_3_1 : Y 10 3 1 = (-1219963203744052188572919/167772160000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_1_3

theorem source_gram_10_3_1 : Z 10 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_3

theorem source_error_10_5_1 : Y 10 5 1 = (1233781148459940320874483/134217728000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_1_5

theorem source_gram_10_5_1 : Z 10 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_5

theorem source_error_10_5_3 : Y 10 5 3 = (-13854999171694482915831/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_3_5

theorem source_gram_10_5_3 : Z 10 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_3_5

theorem source_error_10_7_1 : Y 10 7 1 = (-4673143458544379455879083/335544320000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_1_7

theorem source_gram_10_7_1 : Z 10 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_7

theorem source_error_10_7_3 : Y 10 7 3 = (57805337880323795919969/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_3_7

theorem source_gram_10_7_3 : Z 10 7 3 = (-22680 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_3_7

theorem source_error_10_7_5 : Y 10 7 5 = (-121198635809384297528619/67108864000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_5_7

theorem source_gram_10_7_5 : Z 10 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_5_7

theorem source_error_10_9_1 : Y 10 9 1 = (2012606963507139814961019/83886080000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_1_9

theorem source_gram_10_9_1 : Z 10 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_9

theorem source_error_10_9_3 : Y 10 9 3 = (-52562004903703102850037/5242880000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_3_9

theorem source_gram_10_9_3 : Z 10 9 3 = (90720 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_3_9

theorem source_error_10_9_5 : Y 10 9 5 = (127922353790121014632767/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_5_9

theorem source_gram_10_9_5 : Z 10 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_5_9

theorem source_error_10_9_7 : Y 10 9 7 = (10203611212469228878953/41943040000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_7_9

theorem source_gram_10_9_7 : Z 10 9 7 = (-68040 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_7_9

theorem error_10 : errorRational 10 = candidateY_10 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_10_1_1
  · exact source_error_10_1_3
  · exact source_error_10_1_5
  · exact source_error_10_1_7
  · exact source_error_10_1_9
  · exact source_error_10_3_1
  · exact source_error_10_3_3
  · exact source_error_10_3_5
  · exact source_error_10_3_7
  · exact source_error_10_3_9
  · exact source_error_10_5_1
  · exact source_error_10_5_3
  · exact source_error_10_5_5
  · exact source_error_10_5_7
  · exact source_error_10_5_9
  · exact source_error_10_7_1
  · exact source_error_10_7_3
  · exact source_error_10_7_5
  · exact source_error_10_7_7
  · exact source_error_10_7_9
  · exact source_error_10_9_1
  · exact source_error_10_9_3
  · exact source_error_10_9_5
  · exact source_error_10_9_7
  · exact source_error_10_9_9

theorem gram_10 : gramRational 10 = candidateZ_10 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_10_1_1
  · exact source_gram_10_1_3
  · exact source_gram_10_1_5
  · exact source_gram_10_1_7
  · exact source_gram_10_1_9
  · exact source_gram_10_3_1
  · exact source_gram_10_3_3
  · exact source_gram_10_3_5
  · exact source_gram_10_3_7
  · exact source_gram_10_3_9
  · exact source_gram_10_5_1
  · exact source_gram_10_5_3
  · exact source_gram_10_5_5
  · exact source_gram_10_5_7
  · exact source_gram_10_5_9
  · exact source_gram_10_7_1
  · exact source_gram_10_7_3
  · exact source_gram_10_7_5
  · exact source_gram_10_7_7
  · exact source_gram_10_7_9
  · exact source_gram_10_9_1
  · exact source_gram_10_9_3
  · exact source_gram_10_9_5
  · exact source_gram_10_9_7
  · exact source_gram_10_9_9

end Laughlin.Certificate

end OAI
