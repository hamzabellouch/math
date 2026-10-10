import Mathlib
import OAI.Probability.SKBarriers.Dynamics.HeatBathStationary

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def kernelEvent {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : ℝ := ∑ y : Config n, if A y then discreteKernel β J k x y else 0

theorem kernelEvent_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : 0 ≤ kernelEvent β J A k x := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact discreteKernel_nonneg β J k x y
  · exact le_rfl

theorem kernelEvent_le_one {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] (k : ℕ) (x : Config n) : kernelEvent β J A k x ≤ 1 := by
  rw [← discreteKernel_sum hn β J k x]
  apply Finset.sum_le_sum
  intro y _
  split_ifs
  · exact le_rfl
  · exact discreteKernel_nonneg β J k x y

theorem kernelEvent_zero {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (x : Config n) : kernelEvent β J A 0 x = if A x then 1 else 0 := by
  classical
  unfold kernelEvent
  simp only [discreteKernel]
  by_cases h : A x
  · rw [ite_eq_left h]
    have he (y : Config n) : (if A y then if x=y then (1:ℝ) else 0 else 0) = if x=y then 1 else 0 := by
      by_cases hxy : x=y
      · subst y; simp only [h,ite_true]
      · simp only [ite_eq_right hxy,ite_self]
    simp_rw [he]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : x=y
    · subst y; simp only [ite_eq_right h]
    · simp only [ite_eq_right hxy,ite_self]

theorem kernelEvent_succ {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : kernelEvent β J A (k+1) x =
      ∑ z : Config n, heatBath β J x z*kernelEvent β J A k z := by
  unfold kernelEvent
  simp only [discreteKernel,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp only [Finset.sum_const_zero]

theorem kernelEvent_stationary {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] (k : ℕ) :
    (∑ x : Config n, gibbs β J x*kernelEvent β J A k x) =
      ∑ y : Config n, if A y then gibbs β J y else 0 := by
  unfold kernelEvent
  simp only [Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs
  · exact discreteKernel_stationary hn β J k y
  · exact Finset.sum_const_zero

def occupation {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : ℝ := ∑ i ∈ Finset.range (k+1), kernelEvent β J A i x

theorem occupation_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : 0 ≤ occupation β J A k x :=
  Finset.sum_nonneg (fun i _ => kernelEvent_nonneg β J A i x)

theorem one_le_occupation {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) (hx : A x) : 1 ≤ occupation β J A k x := by
  have H := Finset.single_le_sum (f := fun i => kernelEvent β J A i x)
    (fun i (_ : i ∈ Finset.range (k+1)) => kernelEvent_nonneg β J A i x)
    (show 0 ∈ Finset.range (k+1) by simp)
  simpa only [kernelEvent_zero,ite_eq_left hx,occupation] using H

theorem occupation_recursion {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : occupation β J A (k+1) x =
      kernelEvent β J A 0 x+∑ z : Config n, heatBath β J x z*occupation β J A k z := by
  unfold occupation
  rw [Finset.sum_range_succ']
  simp_rw [kernelEvent_succ,Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem occupation_stationary {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] (k : ℕ) :
    (∑ x : Config n, gibbs β J x*occupation β J A k x) =
      ((k+1:ℕ):ℝ)*(∑ y : Config n, if A y then gibbs β J y else 0) := by
  unfold occupation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [kernelEvent_stationary hn]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [Finset.mul_sum]

end SK.Analytic

end
end

end

end OAI
