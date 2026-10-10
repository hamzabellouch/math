import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Basic

namespace OAI

/-! Fixed rational distributions and their entropy and capacity formulas. -/

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem truncated_polynomial_positive (y : ℚ) (hy : |y| ≤ 1 / 4) :
    0 < ∑ j ∈ Finset.range 17, y ^ j / Nat.factorial j := by
  have term_bound (j : ℕ) :
      |y ^ (j + 1) / (Nat.factorial (j + 1) : ℚ)| ≤ (1 / 4 : ℚ) ^ (j + 1) := by
    have hd : (1 : ℚ) ≤ Nat.factorial (j + 1) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (j + 1)))
    calc
      _ = |y| ^ (j + 1) / (Nat.factorial (j + 1) : ℚ) := by
        simp only [abs_div, abs_pow,
          abs_of_nonneg (Nat.cast_nonneg (Nat.factorial (j + 1)) :
            (0 : ℚ) ≤ (Nat.factorial (j + 1) : ℚ))]
      _ ≤ (1 / 4 : ℚ) ^ (j + 1) / (Nat.factorial (j + 1) : ℚ) := by gcongr
      _ ≤ _ := div_le_self (by positivity) hd
  have hb : |∑ j ∈ Finset.range 16, y ^ (j + 1) / (Nat.factorial (j + 1) : ℚ)| < 1 := by
    calc
      _ ≤ ∑ j ∈ Finset.range 16, |y ^ (j + 1) / (Nat.factorial (j + 1) : ℚ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range 16, (1 / 4 : ℚ) ^ (j + 1) :=
        Finset.sum_le_sum (fun j _ => term_bound j)
      _ < 1 := by norm_num [Finset.sum_range_succ]
  rw [show 17 = 16 + 1 by decide, Finset.sum_range_succ']
  norm_num only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  linarith [(abs_lt.mp hb).1]

theorem weight_positive_of_argument_bound (n : ℤ) (hn : |n| ≤ 160000) :
    0 < weight n := by
  unfold weight
  apply pow_pos
  apply truncated_polynomial_positive
  have hn' : |(n : ℚ)| ≤ 160000 := by exact_mod_cast hn
  rw [abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℚ) < 640000)]
  exact (div_le_iff₀ (by norm_num)).mpr (by linarith)

def weightArguments : List ℤ := 0 :: (tablea ++ tableP ++ tablep ++ tablez)

theorem all_weight_arguments_bounded : ∀ n ∈ weightArguments, |n| ≤ 160000 := by
  decide +kernel

theorem all_weights_positive (n : ℤ) (hn : n ∈ weightArguments) : 0 < weight n :=
  weight_positive_of_argument_bound n (all_weight_arguments_bounded n hn)

theorem normalized_sum {ι : Type} [Fintype ι] (w : ι → ℚ)
    (h : ∑ i, w i ≠ 0) : ∑ i, w i / (∑ j, w j) = 1 := by
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← div_eq_mul_inv, div_self h]

theorem normalized_positive {ι : Type} [Fintype ι] (w : ι → ℚ)
    (hw : ∀ i, 0 < w i) (i : ι) : 0 < w i / (∑ j, w j) := by
  apply div_pos (hw i)
  exact Finset.sum_pos (fun j _ => hw j) ⟨i, Finset.mem_univ i⟩

end MatrixMultiplication.AllFieldParameters

end OAI
