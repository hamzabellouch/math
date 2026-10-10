import OAI.NumberTheory.JointDickman.Counting.EndpointCoefficientMass
import OAI.NumberTheory.JointDickman.Probability.EndpointSplitAverage

namespace OAI

/-! # Pushing the second endpoint's fair split onto its coefficient -/

namespace JointDickman
open Finset

open Classical in
noncomputable def endpointCoefficientTest (B b j q a : ℕ) : ℝ :=
  ∑ c ∈ Ico q (4*q), if a = b+j*c ∧ (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)
    then coefficientWeight B c else 0

theorem endpointCoefficientTest_nonneg (B b j q a : ℕ) :
    0 ≤ endpointCoefficientTest B b j q a := by
  apply sum_nonneg
  intro c _
  split_ifs
  · exact coefficientWeight_nonneg B c
  · rfl

theorem endpointCoefficientTest_ge {B b j q a c : ℕ}
    (hc : c ∈ Ico q (4*q)) (ha : a = b+j*c)
    (hsize : (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)) :
    coefficientWeight B c ≤ endpointCoefficientTest B b j q a := by
  classical
  calc
    _ = (if a = b+j*c ∧ (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)
        then coefficientWeight B c else 0) := by rw [ite_eq_left ⟨ha,hsize⟩]
    _ ≤ _ := single_le_sum (f := fun d => if a = b+j*d ∧ (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) then coefficientWeight B d else 0) (fun d _ => by split_ifs; exact coefficientWeight_nonneg B d; rfl) hc

/-- This identity uses the exact prime-product pushforward, so no local
limit or independence beyond the already constructed endpoint law is assumed. -/
theorem endpointCoefficientTest_mean (B b j q : ℕ) :
    (∑ A ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
        endpointCoefficientTest B b j q (∏ p ∈ A, p)) =
      endpointCoefficientMass B b j q := by
  classical
  unfold endpointCoefficientTest endpointCoefficientMass
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  by_cases hs : (b+j*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B)
  · simp only [hs,ite_true]
    unfold primeProductMass
    rw [sum_mul]
    apply sum_congr rfl
    intro A _
    by_cases ha : (∏ p ∈ A, p) = b+j*c
    · rw [ha]
      simp only [eq_self,true_and,hs,ite_true]
    · simp only [ha,false_and,ite_false,mul_zero,zero_mul]
  · rw [ite_eq_right hs]
    apply sum_eq_zero
    intro A _
    by_cases ha : (∏ p ∈ A, p) = b+j*c
    · rw [ha]
      simp only [eq_self,true_and,hs,ite_false,mul_zero]
    · simp only [ha,false_and,ite_false,mul_zero]

/-- The weighted, independently averaged second endpoint costs B times
its half-prime coefficient mass. -/
theorem independent_endpoint_coefficient_average {B L : ℕ} {τ C : ℝ}
    (hB : 1 < B) (b j q : ℕ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      ∑ A ∈ endpointSplits B L τ C S,
        regularCoefficientWeight B L τ C (∏ p ∈ A, p)*
          regularResidueWeight B L τ C (S \ A)*
            endpointCoefficientTest B b j q (∏ p ∈ A, p)) ≤
      (B : ℝ)*endpointCoefficientMass B b j q := by
  simpa only [endpointCoefficientTest_mean] using
    independent_endpoint_split_average (L := L) (τ := τ) (C := C) hB
      (fun A => endpointCoefficientTest B b j q (∏ p ∈ A, p))
      (fun A _ => endpointCoefficientTest_nonneg B b j q _)

end JointDickman

end OAI
