import OAI.NumberTheory.JointDickman.Arithmetic.PeriodicConvolutionSmoothing

namespace OAI

/-! # A finite square bound for the smoothed coefficient sum -/
namespace JointDickman
open Finset

theorem finite_weighted_square_bound {ι : Type*} (S : Finset ι) (a b : ι → ℂ)
    {C : ℝ} (ha : ∀ i ∈ S, ‖a i‖ ≤ C) :
    ‖∑ i ∈ S, a i*b i‖^2 ≤ (S.card : ℝ)*C^2*∑ i ∈ S, ‖b i‖^2 := by
  have hs := norm_sum_le S (fun i => a i*b i)
  have hc := sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => ‖a i*b i‖)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hc
  apply ((pow_le_pow_left₀ (norm_nonneg _) hs 2).trans hc).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  rw [norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha i hi) 2) (sq_nonneg _)

theorem finite_weighted_square_mean {ι κ : Type*} (I : Finset ι) (S : Finset κ)
    (a b : ι → κ → ℂ) {C X ε : ℝ} (hX : 0 < X)
    (ha : ∀ u ∈ I, ∀ j ∈ S, ‖a u j‖ ≤ C)
    (hb : ∀ j ∈ S, (1/X)*(∑ u ∈ I, ‖b u j‖^2) ≤ ε) :
    (1/X)*(∑ u ∈ I, ‖∑ j ∈ S, a u j*b u j‖^2) ≤ (S.card : ℝ)^2*C^2*ε := by
  calc
    _ ≤ (1/X)*(∑ u ∈ I, (S.card : ℝ)*C^2*∑ j ∈ S, ‖b u j‖^2) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun u hu =>
        finite_weighted_square_bound S (a u) (b u) (ha u hu))) (by positivity)
    _ = (S.card : ℝ)*C^2*∑ j ∈ S, (1/X)*(∑ u ∈ I, ‖b u j‖^2) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro u _
      ring
    _ ≤ (S.card : ℝ)*C^2*∑ _j ∈ S, ε :=
      mul_le_mul_of_nonneg_left (sum_le_sum hb) (by positivity)
    _ = _ := by simp; ring

theorem norm_square_le_twice_difference (a b : ℂ) :
    ‖a‖^2 ≤ 2*‖a-b‖^2+2*‖b‖^2 := by
  have ht : ‖a‖ ≤ ‖a-b‖+‖b‖ := by
    simpa only [sub_add_cancel] using norm_add_le (a-b) b
  nlinarith [norm_nonneg a,norm_nonneg (a-b),norm_nonneg b,sq_nonneg (‖a-b‖-‖b‖)]

end JointDickman

end OAI
