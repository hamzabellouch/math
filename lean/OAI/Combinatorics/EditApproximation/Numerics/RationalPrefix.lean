import OAI.Combinatorics.EditApproximation.Geometry.PrefixCosts
import OAI.Combinatorics.EditApproximation.Numerics.RationalRefinement
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Rational execution and exact real casts of the finite band predictor. -/

namespace EditApproximation

open Finset



theorem rationalConnectionBudget_cast {n : ℕ} (start finish : ℚ) (states : List (TargetInterval n)) :
    (rationalConnectionBudget start states finish : ℝ) = realConnectionBudget start states finish := by
  induction states generalizing start with
  | nil => simp only [rationalConnectionBudget, realConnectionBudget, Rat.cast_abs, Rat.cast_sub]
  | cons state rest ih =>
    simp only [rationalConnectionBudget, realConnectionBudget, Rat.cast_add, Rat.cast_abs,
      Rat.cast_sub, Rat.cast_natCast, ih]



theorem rationalWidePrefixCost_cast {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℚ) (j : ℕ) (p : ℚ) :
    (rationalWidePrefixCost parent r states child j p : ℝ) =
      widePrefixCost parent r states (fun i s => (child i s : ℝ)) j p := by
  simp only [rationalWidePrefixCost, widePrefixCost, Rat.cast_add, Rat.cast_sum,
    rationalConnectionBudget_cast, Rat.cast_natCast]
  congr 1
  apply sum_congr rfl
  intro i hi
  split_ifs <;> simp



theorem rationalWidePrefixMinimum_cast {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℚ) (j : ℕ) (p : ℚ) :
    (rationalWidePrefixMinimum parent r actions hnonempty child j p : ℝ) =
      widePrefixMinimum parent r actions hnonempty (fun i s => (child i s : ℝ)) j p := by
  rw [rationalWidePrefixMinimum, rationalMinimum_cast]
  simp only [widePrefixMinimum, rationalWidePrefixCost_cast, List.map_map, Function.comp_def]

end EditApproximation

end OAI
