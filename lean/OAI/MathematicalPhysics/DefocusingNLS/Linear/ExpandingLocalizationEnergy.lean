import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSobolevLocalization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.LocalizationWeightComparison

namespace OAI

/-! # Uniform two-order localization energy bound

This combines the mixed Fourier estimate with precisely the manuscript's
Y_L weights at s₀ = 6-a and k. It is the finite Fourier energy estimate;
the physical cutoff and Fourier-normalization identification is separate.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

theorem exists_expanding_localization_energy_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (K : 𝓢(EuclideanSpace ℝ (Fin 12), ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (S : Finset frequencyLattice) (v : frequencyLattice → ℂ),
      L ^ (2 * a) * (∫ x, (1 + ‖x‖ ^ 2) ^ (6 - a) *
          ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2) +
        L ^ (12 - 2 * k) * (∫ x, (1 + ‖x‖ ^ 2) ^ k *
          ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2) ≤
        C * ∑ n ∈ S, expandingSobolevWeightSq a k L n * ‖v n‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hlow⟩ := exists_schwartz_sobolev_localization_bound (6 - a) (by linarith) K
  obtain ⟨C₁, hC₁, hhigh⟩ := exists_schwartz_sobolev_localization_bound k (by linarith) K
  refine ⟨C₀ + C₁ * 2 ^ k, by positivity, ?_⟩
  intro L hL S v
  let E : ℝ := ∑ n ∈ S, expandingSobolevWeightSq a k L n * ‖v n‖ ^ 2
  have hlowSum : L ^ (2 * a) * ∑ n ∈ S, (1 + ‖n‖ ^ 2) ^ (6 - a) * ‖v n‖ ^ 2 ≤ E := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (localization_low_weight_le a k L hL n) (sq_nonneg ‖v n‖)
  have hhighSum : L ^ (12 - 2 * k) * ∑ n ∈ S, (1 + ‖n‖ ^ 2) ^ k * ‖v n‖ ^ 2 ≤
      2 ^ k * E := by
    rw [Finset.mul_sum, show 2 ^ k * E =
      ∑ n ∈ S, 2 ^ k * (expandingSobolevWeightSq a k L n * ‖v n‖ ^ 2) by
        dsimp [E]; rw [Finset.mul_sum]]
    apply Finset.sum_le_sum
    intro n _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (localization_high_weight_le a k L ha ha1 hk hL n) (sq_nonneg ‖v n‖)
  have hlo := mul_le_mul_of_nonneg_left (hlow S v).2
    (show 0 ≤ L ^ (2 * a) by positivity)
  have hhi := mul_le_mul_of_nonneg_left (hhigh S v).2
    (show 0 ≤ L ^ (12 - 2 * k) by positivity)
  have hlo' := mul_le_mul_of_nonneg_left hlowSum hC₀
  have hhi' := mul_le_mul_of_nonneg_left hhighSum hC₁
  dsimp [E] at *
  nlinarith

end DefocusingNLS

end OAI
