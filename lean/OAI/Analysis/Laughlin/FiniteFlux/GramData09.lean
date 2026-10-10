import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram09
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow09
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow092
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow093
import OAI.Analysis.Laughlin.FiniteFlux.Data09
import OAI.Analysis.Laughlin.FourBody.NumericBridge
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
theorem source_error_9_1_1 : Y 9 1 1 = (-12465910883340844333323483/6710886400000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 1 0 (by decide),
    source_yRow_eq_rowCompute 9 1 1 1 (by decide),
    source_yRow_eq_rowCompute 9 1 1 2 (by decide),
    source_yRow_eq_rowCompute 9 1 1 3 (by decide),
    source_yRow_eq_rowCompute 9 1 1 4 (by decide),
    source_yRow_eq_rowCompute 9 1 1 5 (by decide),
    source_yRow_eq_rowCompute 9 1 1 6 (by decide),
    computeRow_9_1_1_0, computeRow_9_1_1_1, computeRow_9_1_1_2, computeRow_9_1_1_3, computeRow_9_1_1_4, computeRow_9_1_1_5, computeRow_9_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_1_3 : Y 9 1 3 = (-33961811903853786055197/838860800000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 3 0 (by decide),
    source_yRow_eq_rowCompute 9 1 3 1 (by decide),
    source_yRow_eq_rowCompute 9 1 3 2 (by decide),
    source_yRow_eq_rowCompute 9 1 3 3 (by decide),
    source_yRow_eq_rowCompute 9 1 3 4 (by decide),
    source_yRow_eq_rowCompute 9 1 3 5 (by decide),
    source_yRow_eq_rowCompute 9 1 3 6 (by decide),
    computeRow_9_1_3_0, computeRow_9_1_3_1, computeRow_9_1_3_2, computeRow_9_1_3_3, computeRow_9_1_3_4, computeRow_9_1_3_5, computeRow_9_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_1_5 : Y 9 1 5 = (-670994343426034247927913/6710886400000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 5 0 (by decide),
    source_yRow_eq_rowCompute 9 1 5 1 (by decide),
    source_yRow_eq_rowCompute 9 1 5 2 (by decide),
    source_yRow_eq_rowCompute 9 1 5 3 (by decide),
    source_yRow_eq_rowCompute 9 1 5 4 (by decide),
    source_yRow_eq_rowCompute 9 1 5 5 (by decide),
    source_yRow_eq_rowCompute 9 1 5 6 (by decide),
    computeRow_9_1_5_0, computeRow_9_1_5_1, computeRow_9_1_5_2, computeRow_9_1_5_3, computeRow_9_1_5_4, computeRow_9_1_5_5, computeRow_9_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_1_7 : Y 9 1 7 = (4530779263986412498504797/3355443200000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 7 0 (by decide),
    source_yRow_eq_rowCompute 9 1 7 1 (by decide),
    source_yRow_eq_rowCompute 9 1 7 2 (by decide),
    source_yRow_eq_rowCompute 9 1 7 3 (by decide),
    source_yRow_eq_rowCompute 9 1 7 4 (by decide),
    source_yRow_eq_rowCompute 9 1 7 5 (by decide),
    source_yRow_eq_rowCompute 9 1 7 6 (by decide),
    computeRow_9_1_7_0, computeRow_9_1_7_1, computeRow_9_1_7_2, computeRow_9_1_7_3, computeRow_9_1_7_4, computeRow_9_1_7_5, computeRow_9_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_1_9 : Y 9 1 9 = (2064320406503781558919011/838860800000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 9 0 (by decide),
    source_yRow_eq_rowCompute 9 1 9 1 (by decide),
    source_yRow_eq_rowCompute 9 1 9 2 (by decide),
    source_yRow_eq_rowCompute 9 1 9 3 (by decide),
    source_yRow_eq_rowCompute 9 1 9 4 (by decide),
    source_yRow_eq_rowCompute 9 1 9 5 (by decide),
    source_yRow_eq_rowCompute 9 1 9 6 (by decide),
    computeRow_9_1_9_0, computeRow_9_1_9_1, computeRow_9_1_9_2, computeRow_9_1_9_3, computeRow_9_1_9_4, computeRow_9_1_9_5, computeRow_9_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_3_3 : Y 9 3 3 = (2960534512700301116069433/23488102400000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 3 3 0 (by decide),
    source_yRow_eq_rowCompute 9 3 3 1 (by decide),
    source_yRow_eq_rowCompute 9 3 3 2 (by decide),
    source_yRow_eq_rowCompute 9 3 3 3 (by decide),
    source_yRow_eq_rowCompute 9 3 3 4 (by decide),
    source_yRow_eq_rowCompute 9 3 3 5 (by decide),
    source_yRow_eq_rowCompute 9 3 3 6 (by decide),
    computeRow_9_3_3_0, computeRow_9_3_3_1, computeRow_9_3_3_2, computeRow_9_3_3_3, computeRow_9_3_3_4, computeRow_9_3_3_5, computeRow_9_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_3_5 : Y 9 3 5 = (-249132079557021880785303/11744051200000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 3 5 0 (by decide),
    source_yRow_eq_rowCompute 9 3 5 1 (by decide),
    source_yRow_eq_rowCompute 9 3 5 2 (by decide),
    source_yRow_eq_rowCompute 9 3 5 3 (by decide),
    source_yRow_eq_rowCompute 9 3 5 4 (by decide),
    source_yRow_eq_rowCompute 9 3 5 5 (by decide),
    source_yRow_eq_rowCompute 9 3 5 6 (by decide),
    computeRow_9_3_5_0, computeRow_9_3_5_1, computeRow_9_3_5_2, computeRow_9_3_5_3, computeRow_9_3_5_4, computeRow_9_3_5_5, computeRow_9_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_3_7 : Y 9 3 7 = (-172612848420190308157317/419430400000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 3 7 0 (by decide),
    source_yRow_eq_rowCompute 9 3 7 1 (by decide),
    source_yRow_eq_rowCompute 9 3 7 2 (by decide),
    source_yRow_eq_rowCompute 9 3 7 3 (by decide),
    source_yRow_eq_rowCompute 9 3 7 4 (by decide),
    source_yRow_eq_rowCompute 9 3 7 5 (by decide),
    source_yRow_eq_rowCompute 9 3 7 6 (by decide),
    computeRow_9_3_7_0, computeRow_9_3_7_1, computeRow_9_3_7_2, computeRow_9_3_7_3, computeRow_9_3_7_4, computeRow_9_3_7_5, computeRow_9_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_3_9 : Y 9 3 9 = (-460639144770506834240727/209715200000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 3 9 0 (by decide),
    source_yRow_eq_rowCompute 9 3 9 1 (by decide),
    source_yRow_eq_rowCompute 9 3 9 2 (by decide),
    source_yRow_eq_rowCompute 9 3 9 3 (by decide),
    source_yRow_eq_rowCompute 9 3 9 4 (by decide),
    source_yRow_eq_rowCompute 9 3 9 5 (by decide),
    source_yRow_eq_rowCompute 9 3 9 6 (by decide),
    computeRow_9_3_9_0, computeRow_9_3_9_1, computeRow_9_3_9_2, computeRow_9_3_9_3, computeRow_9_3_9_4, computeRow_9_3_9_5, computeRow_9_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_5_5 : Y 9 5 5 = (-12391755266391716879263611/46976204800000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 5 5 0 (by decide),
    source_yRow_eq_rowCompute 9 5 5 1 (by decide),
    source_yRow_eq_rowCompute 9 5 5 2 (by decide),
    source_yRow_eq_rowCompute 9 5 5 3 (by decide),
    source_yRow_eq_rowCompute 9 5 5 4 (by decide),
    source_yRow_eq_rowCompute 9 5 5 5 (by decide),
    source_yRow_eq_rowCompute 9 5 5 6 (by decide),
    computeRow_9_5_5_0, computeRow_9_5_5_1, computeRow_9_5_5_2, computeRow_9_5_5_3, computeRow_9_5_5_4, computeRow_9_5_5_5, computeRow_9_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_5_7 : Y 9 5 7 = (202846259663372040293217/3355443200000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 5 7 0 (by decide),
    source_yRow_eq_rowCompute 9 5 7 1 (by decide),
    source_yRow_eq_rowCompute 9 5 7 2 (by decide),
    source_yRow_eq_rowCompute 9 5 7 3 (by decide),
    source_yRow_eq_rowCompute 9 5 7 4 (by decide),
    source_yRow_eq_rowCompute 9 5 7 5 (by decide),
    source_yRow_eq_rowCompute 9 5 7 6 (by decide),
    computeRow_9_5_7_0, computeRow_9_5_7_1, computeRow_9_5_7_2, computeRow_9_5_7_3, computeRow_9_5_7_4, computeRow_9_5_7_5, computeRow_9_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_5_9 : Y 9 5 9 = (1717697222431419971099331/838860800000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 5 9 0 (by decide),
    source_yRow_eq_rowCompute 9 5 9 1 (by decide),
    source_yRow_eq_rowCompute 9 5 9 2 (by decide),
    source_yRow_eq_rowCompute 9 5 9 3 (by decide),
    source_yRow_eq_rowCompute 9 5 9 4 (by decide),
    source_yRow_eq_rowCompute 9 5 9 5 (by decide),
    source_yRow_eq_rowCompute 9 5 9 6 (by decide),
    computeRow_9_5_9_0, computeRow_9_5_9_1, computeRow_9_5_9_2, computeRow_9_5_9_3, computeRow_9_5_9_4, computeRow_9_5_9_5, computeRow_9_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_7_7 : Y 9 7 7 = (-3138981013037239731556773/1677721600000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 7 7 0 (by decide),
    source_yRow_eq_rowCompute 9 7 7 1 (by decide),
    source_yRow_eq_rowCompute 9 7 7 2 (by decide),
    source_yRow_eq_rowCompute 9 7 7 3 (by decide),
    source_yRow_eq_rowCompute 9 7 7 4 (by decide),
    source_yRow_eq_rowCompute 9 7 7 5 (by decide),
    source_yRow_eq_rowCompute 9 7 7 6 (by decide),
    computeRow_9_7_7_0, computeRow_9_7_7_1, computeRow_9_7_7_2, computeRow_9_7_7_3, computeRow_9_7_7_4, computeRow_9_7_7_5, computeRow_9_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_7_9 : Y 9 7 9 = (-1034085603218724160418079/419430400000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 7 9 0 (by decide),
    source_yRow_eq_rowCompute 9 7 9 1 (by decide),
    source_yRow_eq_rowCompute 9 7 9 2 (by decide),
    source_yRow_eq_rowCompute 9 7 9 3 (by decide),
    source_yRow_eq_rowCompute 9 7 9 4 (by decide),
    source_yRow_eq_rowCompute 9 7 9 5 (by decide),
    source_yRow_eq_rowCompute 9 7 9 6 (by decide),
    computeRow_9_7_9_0, computeRow_9_7_9_1, computeRow_9_7_9_2, computeRow_9_7_9_3, computeRow_9_7_9_4, computeRow_9_7_9_5, computeRow_9_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_9_9 : Y 9 9 9 = (-9956547203160990435022917/104857600000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 9 9 0 (by decide),
    source_yRow_eq_rowCompute 9 9 9 1 (by decide),
    source_yRow_eq_rowCompute 9 9 9 2 (by decide),
    source_yRow_eq_rowCompute 9 9 9 3 (by decide),
    source_yRow_eq_rowCompute 9 9 9 4 (by decide),
    source_yRow_eq_rowCompute 9 9 9 5 (by decide),
    source_yRow_eq_rowCompute 9 9 9 6 (by decide),
    computeRow_9_9_9_0, computeRow_9_9_9_1, computeRow_9_9_9_2, computeRow_9_9_9_3, computeRow_9_9_9_4, computeRow_9_9_9_5, computeRow_9_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_9_1_1 : Z 9 1 1 = (80640 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_1_1

theorem source_gram_9_1_3 : Z 9 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_1_3

theorem source_gram_9_1_5 : Z 9 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_1_5

theorem source_gram_9_1_7 : Z 9 1 7 = (-10080 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_1_7

theorem source_gram_9_1_9 : Z 9 1 9 = (136080 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_1_9

theorem source_gram_9_3_3 : Z 9 3 3 = (4320 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_3_3

theorem source_gram_9_3_5 : Z 9 3 5 = (-2160 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_3_5

theorem source_gram_9_3_7 : Z 9 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_3_7

theorem source_gram_9_3_9 : Z 9 3 9 = (22680 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_3_9

theorem source_gram_9_5_5 : Z 9 5 5 = (1080 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_5_5

theorem source_gram_9_5_7 : Z 9 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_5_7

theorem source_gram_9_5_9 : Z 9 5 9 = (-11340 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_5_9

theorem source_gram_9_7_7 : Z 9 7 7 = (1260 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_7_7

theorem source_gram_9_7_9 : Z 9 7 9 = (-17010 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_7_9

theorem source_gram_9_9_9 : Z 9 9 9 = (348705 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_9_9

theorem source_error_9_3_1 : Y 9 3 1 = (-33961811903853786055197/838860800000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_1_3

theorem source_gram_9_3_1 : Z 9 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_1_3

theorem source_error_9_5_1 : Y 9 5 1 = (-670994343426034247927913/6710886400000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_1_5

theorem source_gram_9_5_1 : Z 9 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_1_5

theorem source_error_9_5_3 : Y 9 5 3 = (-249132079557021880785303/11744051200000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_3_5

theorem source_gram_9_5_3 : Z 9 5 3 = (-2160 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_3_5

theorem source_error_9_7_1 : Y 9 7 1 = (4530779263986412498504797/3355443200000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_1_7

theorem source_gram_9_7_1 : Z 9 7 1 = (-10080 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_1_7

theorem source_error_9_7_3 : Y 9 7 3 = (-172612848420190308157317/419430400000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_3_7

theorem source_gram_9_7_3 : Z 9 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_3_7

theorem source_error_9_7_5 : Y 9 7 5 = (202846259663372040293217/3355443200000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_5_7

theorem source_gram_9_7_5 : Z 9 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_5_7

theorem source_error_9_9_1 : Y 9 9 1 = (2064320406503781558919011/838860800000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_1_9

theorem source_gram_9_9_1 : Z 9 9 1 = (136080 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_1_9

theorem source_error_9_9_3 : Y 9 9 3 = (-460639144770506834240727/209715200000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_3_9

theorem source_gram_9_9_3 : Z 9 9 3 = (22680 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_3_9

theorem source_error_9_9_5 : Y 9 9 5 = (1717697222431419971099331/838860800000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_5_9

theorem source_gram_9_9_5 : Z 9 9 5 = (-11340 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_5_9

theorem source_error_9_9_7 : Y 9 9 7 = (-1034085603218724160418079/419430400000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_7_9

theorem source_gram_9_9_7 : Z 9 9 7 = (-17010 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_7_9

theorem error_9 : errorRational 9 = candidateY_9 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_9_1_1
  · exact source_error_9_1_3
  · exact source_error_9_1_5
  · exact source_error_9_1_7
  · exact source_error_9_1_9
  · exact source_error_9_3_1
  · exact source_error_9_3_3
  · exact source_error_9_3_5
  · exact source_error_9_3_7
  · exact source_error_9_3_9
  · exact source_error_9_5_1
  · exact source_error_9_5_3
  · exact source_error_9_5_5
  · exact source_error_9_5_7
  · exact source_error_9_5_9
  · exact source_error_9_7_1
  · exact source_error_9_7_3
  · exact source_error_9_7_5
  · exact source_error_9_7_7
  · exact source_error_9_7_9
  · exact source_error_9_9_1
  · exact source_error_9_9_3
  · exact source_error_9_9_5
  · exact source_error_9_9_7
  · exact source_error_9_9_9

theorem gram_9 : gramRational 9 = candidateZ_9 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_9_1_1
  · exact source_gram_9_1_3
  · exact source_gram_9_1_5
  · exact source_gram_9_1_7
  · exact source_gram_9_1_9
  · exact source_gram_9_3_1
  · exact source_gram_9_3_3
  · exact source_gram_9_3_5
  · exact source_gram_9_3_7
  · exact source_gram_9_3_9
  · exact source_gram_9_5_1
  · exact source_gram_9_5_3
  · exact source_gram_9_5_5
  · exact source_gram_9_5_7
  · exact source_gram_9_5_9
  · exact source_gram_9_7_1
  · exact source_gram_9_7_3
  · exact source_gram_9_7_5
  · exact source_gram_9_7_7
  · exact source_gram_9_7_9
  · exact source_gram_9_9_1
  · exact source_gram_9_9_3
  · exact source_gram_9_9_5
  · exact source_gram_9_9_7
  · exact source_gram_9_9_9

end Laughlin.Certificate

end OAI
