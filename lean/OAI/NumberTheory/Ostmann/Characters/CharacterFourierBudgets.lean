import OAI.NumberTheory.Ostmann.Characters.CharacterPrimeFrequency
import OAI.NumberTheory.Ostmann.Construction.WordTransferUniformCoefficient
import OAI.NumberTheory.Ostmann.Construction.DyadicPrimeRange

namespace OAI

/-! # Explicit finite-frequency and Fourier-window costs -/
namespace Ostmann
open scoped Classical
open scoped FourierTransform SchwartzMap

theorem naturalTransferCutoff_linear_bound (k j : ℕ) (d m : ℝ)
    (hj : j ≤ k) (hd : 0 ≤ d) (hm : 1 ≤ m) :
    (naturalTransferCutoff (d * m) m j : ℝ) ≤
      Real.exp (((2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k) * m) := by
  exact (Nat.floor_le (Real.exp_nonneg _)).trans
    (Real.exp_le_exp.mpr (transferErrorScale_linear_bound k j d m hj hd hm))

theorem character_initial_window_bounds (d C m : ℝ)
    (hd : 1 ≤ d) (hm : 1 ≤ m) (hC : 0 ≤ C) (hCm : C ≤ m) :
    1 ≤ Real.exp (d * m - C) ∧
      Real.exp (d * m - C) ≤ Real.exp (d * m + C) ∧
      Real.exp (d * m + C) - Real.exp (d * m - C) ≤ Real.exp ((d + 1) * m) := by
  have hm0 : 0 ≤ m := by linarith
  have hdm : m ≤ d * m := by nlinarith only [hd, hm0]
  refine ⟨Real.one_le_exp_iff.mpr (by linarith),
    Real.exp_le_exp.mpr (by linarith), ?_⟩
  apply (sub_le_self _ (Real.exp_nonneg _)).trans
  exact Real.exp_le_exp.mpr (by nlinarith only [hCm])

theorem character_uniform_profile_bounds (n : ℕ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi S : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hs₀ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ S)
    (hs₁ : SchwartzMap.seminorm ℝ 0 1 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ S) :
    let FP := WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    SchwartzMap.seminorm ℝ 0 0 FP.profile ≤ S ∧
      SchwartzMap.seminorm ℝ 0 1 FP.profile ≤ S := ⟨hs₀, hs₁⟩

theorem character_prime_band_log_ratio (α β L M H : ℝ)
    (hL : 0 ≤ L) (hLM : L ≤ M) (_hβ : 0 ≤ β) (hH : β - α ≤ H) (hH0 : 0 ≤ H) :
    Real.log (Real.exp (Real.exp (β * L))) / Real.exp (α * L) ≤
      Real.exp (H * (1 + M)) := by
  rw [Real.log_exp, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_right hH hL
  have h₂ := mul_le_mul_of_nonneg_left hLM hH0
  nlinarith only [h₁, h₂, hH0]

theorem character_prime_band_dyadic_budget (E : ℕ) (β L M H : ℝ)
    (hβ : 0 ≤ β) (hL : 1 ≤ L) (hLM : L ≤ M)
    (hH : β + Real.log ((Real.log 2)⁻¹ + 1) ≤ H) (hH0 : 0 ≤ H)
    (hE : (E : ℝ) ≤ Real.exp (Real.exp (β * L))) :
    ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)) := by
  apply (dyadic_prime_range_count E β L hβ hL hE).trans
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_right hH (by linarith : 0 ≤ L)
  have h₂ := mul_le_mul_of_nonneg_left hLM hH0
  nlinarith only [h₁, h₂, hH0]

end Ostmann

end OAI
