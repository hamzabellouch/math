import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

theorem density_power_bound {B U σ : ℝ} (hB : 1 ≤ B) (hBU : B ≤ U)
    (hU : U ≤ 512 * B^5) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (U+B)*U*U^(-2*σ) ≤ (2*512^2 : ℝ)*B^(10*(1-σ)) := by
  have hBp : 0 < B := by linarith
  have hUp : 0 < U := lt_of_lt_of_le hBp hBU
  have ha : 0 ≤ 2*(1-σ) := by positivity
  have hb : 2*(1-σ) ≤ 2 := by linarith
  have hp : U^2*U^(-2*σ) = U^(2*(1-σ)) := by
    rw [← Real.rpow_natCast U 2, ← Real.rpow_add hUp]
    congr 1
    ring
  have hc : (512 : ℝ)^(2*(1-σ)) ≤ 512^2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 512) hb
  calc
    (U+B)*U*U^(-2*σ) ≤ (2*U)*U*U^(-2*σ) := by
      gcongr
      linarith
    _ = 2*U^(2*(1-σ)) := by rw [show 2*U*U = 2*U^2 by ring, mul_assoc, hp]
    _ ≤ 2*(512*B^5)^(2*(1-σ)) := by gcongr
    _ = 2*((512:ℝ)^(2*(1-σ))*B^(10*(1-σ))) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_natCast B 5, ← Real.rpow_mul hBp.le]
      congr 3
      ring
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num))
        (Real.rpow_nonneg hBp.le _)

theorem density_sum_bound {J : ℕ} {B L D σ A : ℝ} (U : ℕ → ℝ)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (_hD : 0 ≤ D)
    (hJ : (J:ℝ) ≤ D*L) (hA0 : 0 ≤ A) (hA : A ≤ L)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hU : ∀ j ∈ Finset.range J, B ≤ U j ∧ U j ≤ 512*B^5)
    (hlog0 : ∀ j ∈ Finset.range J, 0 ≤ 1+Real.log (2*U j))
    (hlog : ∀ j ∈ Finset.range J, 1+Real.log (2*U j) ≤ 2048*L) :
    4*(J:ℝ)*∑ j ∈ Finset.range J,
      (U j+B)*A*(1+Real.log (2*U j))^7*U j*(U j)^(-2*σ) ≤
        (8*512^2*2048^7*D^2)*B^(10*(1-σ))*L^10 := by
  have hLn : 0 ≤ L := by linarith
  have hterm (j : ℕ) (hj : j ∈ Finset.range J) :
      (U j+B)*A*(1+Real.log (2*U j))^7*U j*(U j)^(-2*σ) ≤
        (2*512^2)*2048^7*B^(10*(1-σ))*L^8 := by
    have hp := density_power_bound hB (hU j hj).1 (hU j hj).2 hσ hσ1
    calc
      _ = ((U j+B)*U j*(U j)^(-2*σ))*A*(1+Real.log (2*U j))^7 := by ring
      _ ≤ ((2*512^2)*B^(10*(1-σ)))*L*(2048*L)^7 := by
        apply mul_le_mul
        · exact mul_le_mul hp hA hA0 (by positivity)
        · exact pow_le_pow_left₀ (hlog0 j hj) (hlog j hj) 7
        · exact pow_nonneg (hlog0 j hj) 7
        · positivity
      _ = _ := by ring
  calc
    _ ≤ 4*(J:ℝ)*∑ _j ∈ Finset.range J,
        (2*512^2)*2048^7*B^(10*(1-σ))*L^8 := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = 4*(J:ℝ)^2*((2*512^2)*2048^7*B^(10*(1-σ))*L^8) := by simp; ring
    _ ≤ 4*(D*L)^2*((2*512^2)*2048^7*B^(10*(1-σ))*L^8) := by gcongr
    _ = _ := by ring

end Ostmann.ZeroDensity

end

end OAI
