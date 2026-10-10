import OAI.NumberTheory.JointDickman.Analysis.FairLaplaceFeature
import OAI.NumberTheory.JointDickman.Amplification.LogIntervalApproximation

namespace OAI

/-! # Polynomial tests of the exponential log coordinate -/
namespace JointDickman
open Finset Classical

theorem polynomial_log_expansion (P : Polynomial ℝ) {r : ℝ} (hr : 0 < r) (B : ℝ) :
    P.eval (Real.exp (-(Real.log r/B))) =
      ∑ v ∈ range (P.natDegree+1), P.coeff v*r^(-(v : ℝ)/B) := by
  rw [Polynomial.eval_eq_sum_range]
  apply sum_congr rfl
  intro v _
  rw [← Real.exp_nat_mul,Real.rpow_def_of_pos hr]
  congr 2
  ring

theorem fairSplitAverage_polynomial (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (P : Polynomial ℝ) (B : ℝ) (x : Q → Bool) :
    fairSplitAverage x (fun y =>
      P.eval (Real.exp (-(Real.log (retainedPrimeProduct Q y)/B)))) =
      ∑ v ∈ range (P.natDegree+1), P.coeff v*primeLaplaceFeature Q B v x := by
  have he (y : Q → Bool) := polynomial_log_expansion P
    (by exact_mod_cast retainedPrimeProduct_pos Q hQ y : (0 : ℝ) < (retainedPrimeProduct Q y : ℝ)) B
  simp_rw [he]
  exact fairSplitAverage_laplace_sum Q B _ _ x

end JointDickman

end OAI
