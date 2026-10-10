import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI


namespace InternalCatalan

open scoped BigOperators

theorem finitePlace_log_two_lt : Real.log 2 < (693149 / 1000000 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
  have h := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 693149 / 1000000) 8
  have hs : (2 : ℝ) < ∑ i ∈ Finset.range 8,
      (693149 / 1000000 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hs.trans_le h

theorem finitePlace_constant_gt_threshold :
    -(229084 / 100000 : ℝ) <
      -(8609 / 4608 : ℝ) -
        ((1 / 2 : ℝ) + (505 / 4608 : ℝ)) * Real.log 2 := by
  linarith [finitePlace_log_two_lt]

theorem finitePlace_realPlace_threshold_gap :
    -(22909 / 10000 : ℝ) < -(229084 / 100000 : ℝ) := by
  norm_num

end InternalCatalan

end OAI
