import OAI.Combinatorics.ContingencyTables.Dense.DenseRational
import Mathlib.Data.Fintype.Fin

namespace OAI

/-! # Exact finite-bit Metropolis acceptance

A uniform integer encoded by the allotted fair bits is compared with a
power of two. Extra bits are padding; their number does not change the
acceptance probability.
-/

namespace ContingencyTables.FairBits

open scoped BigOperators

abbrev acceptDyadic (gap allowance : ℕ) (z : Fin (2 ^ allowance)) : Prop :=
  z.val < 2 ^ (allowance - gap)

theorem acceptDyadic_count (gap allowance : ℕ) :
    (Finset.univ.filter (acceptDyadic gap allowance)).card = 2 ^ (allowance - gap) := by
  change (Finset.univ.filter (fun z : Fin (2 ^ allowance) => z.val < 2 ^ (allowance - gap))).card = _
  rw [Fin.card_filter_val_lt, min_eq_right]
  exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)

theorem acceptDyadic_probability (gap allowance : ℕ) (h : gap ≤ allowance) :
    ((Finset.univ.filter (acceptDyadic gap allowance)).card : ℝ) / (2 : ℝ) ^ allowance =
      1 / (2 : ℝ) ^ gap := by
  rw [acceptDyadic_count gap allowance, Nat.cast_pow, Nat.cast_ofNat]
  have ha : allowance = (allowance - gap) + gap := by omega
  have hden : (2 : ℝ) ^ allowance = 2 ^ (allowance - gap) * 2 ^ gap := by
    conv_lhs => rw [ha, pow_add]
  rw [hden]
  simpa only [one_div] using div_mul_cancel_left₀
    (by positivity : (2 : ℝ) ^ (allowance - gap) ≠ 0) ((2 : ℝ) ^ gap)

theorem dyadic_ratio_min (a b : ℕ) :
    min (1 : ℝ) ((1 / (2 : ℝ) ^ b) / (1 / (2 : ℝ) ^ a)) =
      1 / (2 : ℝ) ^ (b - a) := by
  by_cases hab : a ≤ b
  · have he : b = a + (b - a) := by omega
    have hr : ((1 / (2 : ℝ) ^ b) / (1 / (2 : ℝ) ^ a)) = 1 / (2 : ℝ) ^ (b - a) := by
      conv_lhs => rw [he, pow_add]
      field_simp
    rw [hr, min_eq_right]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show (1 : ℝ) ≤ 2 ^ (b - a) from one_le_pow₀ (by norm_num))
  · have hba : b ≤ a := by omega
    have he : a = b + (a - b) := by omega
    have hr : ((1 / (2 : ℝ) ^ b) / (1 / (2 : ℝ) ^ a)) = (2 : ℝ) ^ (a - b) := by
      conv_lhs => rw [he, pow_add]
      field_simp
    rw [hr, Nat.sub_eq_zero_of_le hba, pow_zero, div_one, min_eq_left]
    exact one_le_pow₀ (by norm_num)

end ContingencyTables.FairBits

namespace ContingencyTables.GridBoundary

open scoped Classical

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q K : ℕ}

theorem dense_acceptance_dyadic (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) K) :
    min (1 : ℝ) (denseBinWeight R P d e b / denseBinWeight R P d e a) =
      1 / (2 : ℝ) ^ (denseExponent R P d e b - denseExponent R P d e a) := by
  simp only [denseBinWeight_eq_dyadic]
  exact FairBits.dyadic_ratio_min _ _

end ContingencyTables.GridBoundary

end OAI
