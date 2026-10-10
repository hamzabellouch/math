import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-! # Finite geometric estimates for the block truncation -/
namespace JointDickman
open Finset

 theorem brun_weighted_geometric (N : ℕ) :
    (∑ j ∈ range N, ((j:ℝ)+1)/(2:ℝ)^j) = 4-2*((N:ℝ)+2)/(2:ℝ)^N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ,ih,pow_succ]
    push_cast
    field_simp
    ring

 theorem brun_weighted_geometric_le (N : ℕ) :
    (∑ j ∈ range N, ((j:ℝ)+1)/(2:ℝ)^j) ≤ 4 := by
  rw [brun_weighted_geometric]
  have : 0 ≤ 2*((N:ℝ)+2)/(2:ℝ)^N := by positivity
  linarith

 theorem brun_geometric (N : ℕ) :
    (∑ j ∈ range N, 1/(4:ℝ)^(j+1)) = (1-1/(4:ℝ)^N)/3 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ,ih,pow_succ]
    field_simp
    ring

 theorem brun_geometric_le (N : ℕ) : (∑ j ∈ range N, 1/(4:ℝ)^(j+1)) ≤ 1 := by
  rw [brun_geometric]
  have : 0 ≤ 1/(4:ℝ)^N := by positivity
  linarith

end JointDickman

end OAI
