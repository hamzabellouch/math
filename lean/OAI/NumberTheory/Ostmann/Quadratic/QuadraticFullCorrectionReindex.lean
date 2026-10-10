import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullLowGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullHighGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullMiddleGrowth

namespace OAI

/-! # The literal frequency-first corrections are the bounded full sums -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_weighted_filter_sum (S T : Finset ℕ) (P : ℕ → ℕ → Prop)
    (c : ℕ → ℂ) (f : ℕ → ℕ → ℂ) :
    (∑ b ∈ S, c b * ∑ d ∈ T.filter (fun d => P d b), f d b) =
      ∑ d ∈ T, ∑ b ∈ S, if P d b then c b * f d b else 0 := by
  classical
  simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  exact Finset.sum_comm

theorem quadratic_full_low_reindex (M H J : ℝ) (e N Q K : ℕ) (v w : ℕ → ℂ) :
    (∑ b ∈ oddSquarefreeRange K,
      ∑ d ∈ (Finset.Icc 1 Q).filter (fun d : ℕ =>
        (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J),
        (ArithmeticFunction.moebius d : ℂ) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
          (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b) =
      quadraticFullLowCorrection M H J e N Q K (fun _ _ => True) v w := by
  simpa only [one_mul, true_and, quadraticFullLowCorrection] using
    quadratic_weighted_filter_sum (oddSquarefreeRange K) (Finset.Icc 1 Q)
      (fun d b => (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J)
      (fun _ => 1) (fun d b => (ArithmeticFunction.moebius d : ℂ) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d
          (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b)

theorem quadratic_full_high_reindex (M H J : ℝ) (e N Q K : ℕ) (v w : ℕ → ℂ) :
    (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) *
      ∑ d ∈ (Finset.Icc 1 Q).filter (fun d : ℕ =>
        quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ)),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w b) =
      quadraticFullHighCorrection M H J e N Q K (fun _ _ => True) v w := by
  rw [quadratic_weighted_filter_sum]
  unfold quadraticFullHighCorrection
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro b _
  simp only [true_and]
  split_ifs <;> ring

theorem quadratic_full_middle_reindex (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M H J : ℝ) (e N Q K L : ℕ) (v w : ℕ → ℂ) :
    (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) *
      ∑ d ∈ (Finset.Icc 1 Q).filter (fun d : ℕ =>
        quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
        (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticMiddleWindow ρ a ha M e N d v w b L) =
      quadraticFullMiddleCorrection ρ a ha M H J e N Q K L (fun _ _ => True) v w := by
  classical
  simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  unfold quadraticFullMiddleCorrection
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro b _
  simp only [true_and]
  split_ifs <;> ring

end Ostmann

end OAI
