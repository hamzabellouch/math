import OAI.NumberTheory.JointDickman.Amplification.FiniteWeightedSquare

namespace OAI

/-! # Passing from small short-average energy to a finite coefficient sum -/
namespace JointDickman
open Finset

theorem finite_approximation_square_mean {ι κ : Type*} (I : Finset ι) (S : Finset κ)
    (f : ι → ℂ) (a b : ι → κ → ℂ) {X E C ε : ℝ}
    (hX : 0 < X) (hI : (I.card : ℝ) ≤ 2*X)
    (hf : ∀ u ∈ I, ‖f u-∑ j ∈ S, a u j*b u j‖ ≤ E)
    (ha : ∀ u ∈ I, ∀ j ∈ S, ‖a u j‖ ≤ C)
    (hb : ∀ j ∈ S, (1/X)*(∑ u ∈ I, ‖b u j‖^2) ≤ ε) :
    (1/X)*(∑ u ∈ I, ‖f u‖^2) ≤ 4*E^2+2*(S.card : ℝ)^2*C^2*ε := by
  have hpoint (u) (hu : u ∈ I) : ‖f u‖^2 ≤ 2*E^2+2*‖∑ j ∈ S, a u j*b u j‖^2 := by
    have ht := norm_square_le_twice_difference (f u) (∑ j ∈ S, a u j*b u j)
    have hp : ‖f u-∑ j ∈ S, a u j*b u j‖^2 ≤ E^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hf u hu) 2
    have hp2 := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2 by norm_num)
    exact ht.trans (add_le_add hp2 le_rfl)
  have hmean := finite_weighted_square_mean I S a b hX ha hb
  calc
    _ ≤ (1/X)*(∑ u ∈ I, (2*E^2+2*‖∑ j ∈ S, a u j*b u j‖^2)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hpoint) (by positivity)
    _ = (2*(I.card : ℝ)/X)*E^2+2*((1/X)*(∑ u ∈ I, ‖∑ j ∈ S, a u j*b u j‖^2)) := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum]
      ring
    _ ≤ 4*E^2+2*((S.card : ℝ)^2*C^2*ε) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg E)
        apply (div_le_iff₀ hX).mpr
        linarith
      · exact mul_le_mul_of_nonneg_left hmean (by norm_num)
    _ = _ := by ring

theorem succ_card_scaled_square {T : ℕ} (hT : 0 < T) (C : ℝ) :
    ((T : ℝ)+1)^2*(C/(T : ℝ))^2 ≤ 4*C^2 := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hr : ((T : ℝ)+1)/(T : ℝ) ≤ 2 := (div_le_iff₀ hT0).mpr (by linarith)
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hr 2) (sq_nonneg C)
  convert hp using 1 <;> ring

end JointDickman

end OAI
