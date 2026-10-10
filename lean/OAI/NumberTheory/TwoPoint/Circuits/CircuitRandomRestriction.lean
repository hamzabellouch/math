import OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionFourier
import OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionSurvival
import OAI.NumberTheory.TwoPoint.Circuits.CircuitDecisionTree

namespace OAI

/-! Transfer from low-degree approximation after a random restriction to
the Fourier tail of the original function. All probability spaces are finite. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem restriction_fourier_average {n : ℕ} (f : BooleanCube n → ℝ)
    (μ : FiniteLaw (BooleanCube n)) (t : ℕ) :
    μ.average (fun mask => cubeAverage (fun y => cubeAverage (fun x =>
      (f (restrictCube (sampledCoordinates mask) y x) -
        walshTruncation (fun z => f (restrictCube (sampledCoordinates mask) y z)) t x) ^ 2))) =
      ∑ S : Finset (Fin n), (walshCoefficient f S) ^ 2 *
        μ.probability (fun mask => t < (S ∩ sampledCoordinates mask).card) := by
  simp_rw [restricted_fourier_tail_mean, sum_filter]
  rw [μ.average_sum]
  apply sum_congr rfl
  intro S _
  have heq : (fun mask : BooleanCube n =>
      if t < (S ∩ sampledCoordinates mask).card then (walshCoefficient f S) ^ 2 else 0) =
      fun mask => (if t < (S ∩ sampledCoordinates mask).card then (1 : ℝ) else 0) *
        (walshCoefficient f S) ^ 2 := by
    funext mask
    split_ifs <;> simp
  rw [heq, μ.average_mul_const]
  rw [mul_comm]
  congr 1
  unfold FiniteLaw.probability
  apply congrArg μ.average
  funext mask
  by_cases h : t < (S ∩ sampledCoordinates mask).card <;> simp [h]

theorem fourier_tail_le_random_restriction {n : ℕ} (f : BooleanCube n → ℝ)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t d : ℕ)
    (ht : 2 * (t : ℝ) ≤ p * (d + 1)) (hd : 8 ≤ p * (d + 1)) :
    cubeAverage (fun x => (f x - walshTruncation f d x) ^ 2) ≤
      2 * (bernoulliCubeLaw n p hp hp1).average (fun mask =>
        cubeAverage (fun y => cubeAverage (fun x =>
          (f (restrictCube (sampledCoordinates mask) y x) -
            walshTruncation (fun z => f (restrictCube (sampledCoordinates mask) y z)) t x) ^ 2))) := by
  rw [walshTruncation_error, restriction_fourier_average, sum_filter, mul_sum]
  apply sum_le_sum
  intro S _
  by_cases hS : d < S.card
  · rw [ite_eq_left hS]
    have hcard : (d : ℝ) + 1 ≤ S.card := by exact_mod_cast hS
    have hmul := mul_le_mul_of_nonneg_left hcard hp
    have hsurv := bernoulli_support_survival p hp hp1 S t (ht.trans hmul) (hd.trans hmul)
    have h := mul_le_mul_of_nonneg_left hsurv (sq_nonneg (walshCoefficient f S))
    nlinarith
  · rw [ite_eq_right hS]
    exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
      ((bernoulliCubeLaw n p hp hp1).probability_nonneg _))

lemma walshTruncation_error_le_square {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) :
    cubeAverage (fun x => (f x - walshTruncation f t x) ^ 2) ≤
      cubeAverage (fun x => (f x) ^ 2) := by
  rw [walshTruncation_error, walsh_parseval]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun S _ _ => sq_nonneg (walshCoefficient f S))

lemma walshTruncation_error_eq_zero {n t : ℕ} {f : BooleanCube n → ℝ}
    (hf : WalshDegreeLE f t) :
    cubeAverage (fun x => (f x - walshTruncation f t x) ^ 2) = 0 := by
  rw [walshTruncation_error]
  apply sum_eq_zero
  intro S hS
  rw [hf.high_coefficient_zero S (mem_filter.mp hS).2]
  simp

end TwoPointCorrelations

end OAI
