import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicSimplexCutoff

namespace OAI

/-! # Inclusion-exclusion satisfies the Dickman integral recurrence -/
namespace JointDickman
open Finset MeasureTheory

 theorem logarithmicAvoidance_succ {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (N : ℕ) :
    logarithmicAvoidance (N+1) c =
      1 - ∫ s in c..1, logarithmicAvoidance N (s/(1-s))/s := by
  have hi (n : ℕ) : IntervalIntegrable
      (fun s => (-1 : ℝ)^n * (logarithmicSimplex n (s/(1-s))/s)) volume c 1 :=
    (logarithmicSimplex_integrable hc hc1 n).const_mul _
  have hs : (∫ s in c..1, logarithmicAvoidance N (s/(1-s))/s) =
      ∑ n ∈ range (N+1), (-1 : ℝ)^n * logarithmicSimplex (n+1) c := by
    simp only [logarithmicAvoidance, sum_div]
    simp_rw [mul_div_assoc]
    rw [intervalIntegral.integral_finsetSum (fun n _ => hi n)]
    apply sum_congr rfl
    intro n _
    rw [intervalIntegral.integral_const_mul, ← logarithmicSimplex_succ hc hc1]
  rw [hs, logarithmicAvoidance, sum_range_succ']
  simp only [pow_zero, logarithmicSimplex_zero, one_mul]
  have he : (∑ k ∈ range (N+1), (-1 : ℝ)^(k+1)*logarithmicSimplex (k+1) c) =
      -(∑ k ∈ range (N+1), (-1 : ℝ)^k*logarithmicSimplex (k+1) c) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  rw [he]
  ring

end JointDickman

end OAI
