import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ProbabilityTheory

namespace Problem336AdditiveD139.InnovationErrorScale

def errorConstant (L σ c₃ : ℝ) : ℝ :=
  L * σ + L ^ 2 / 2 + (2 / 3 : ℝ) * (c₃ * σ ^ 3 + L ^ 3) + σ ^ 4 / 4

theorem errorConstant_nonneg {L σ c₃ : ℝ}
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hc : 0 ≤ c₃) :
    0 ≤ errorConstant L σ c₃ := by
  unfold errorConstant
  positivity

theorem higher_powers_le (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    h ^ 2 ≤ h * Real.sqrt h ∧ h ^ 3 ≤ h * Real.sqrt h := by
  have hs0 := Real.sqrt_nonneg h
  have hs1 : Real.sqrt h ≤ 1 := by simpa using Real.sqrt_le_sqrt h1
  have hsq := Real.sq_sqrt h0
  have hhs : h ≤ Real.sqrt h := by nlinarith
  have h2 : h ^ 2 ≤ h * Real.sqrt h := by nlinarith
  have h3 : h ^ 3 ≤ h ^ 2 := by nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr h1)]
  exact ⟨h2, h3.trans h2⟩

theorem moment_error_le_scale {L σ c₃ h : ℝ}
    (hL : 0 ≤ L) (_hσ : 0 ≤ σ) (_hc : 0 ≤ c₃) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    (2 * (L * h) * (σ * Real.sqrt h) + (L * h) ^ 2) / 2 +
        4 * (c₃ * σ ^ 3 * h * Real.sqrt h + (L * h) ^ 3) / 6 +
        (h * σ ^ 2) ^ 2 / 4 ≤ errorConstant L σ c₃ * h * Real.sqrt h := by
  obtain ⟨h2, h3⟩ := higher_powers_le h h0 h1
  have hA : 0 ≤ L ^ 2 / 2 + σ ^ 4 / 4 := by positivity
  have hB : 0 ≤ (2 / 3 : ℝ) * L ^ 3 := by positivity
  calc
    _ = (L * σ + (2 / 3 : ℝ) * c₃ * σ ^ 3) * (h * Real.sqrt h) +
        (L ^ 2 / 2 + σ ^ 4 / 4) * h ^ 2 + (2 / 3 : ℝ) * L ^ 3 * h ^ 3 := by ring
    _ ≤ (L * σ + (2 / 3 : ℝ) * c₃ * σ ^ 3) * (h * Real.sqrt h) +
        (L ^ 2 / 2 + σ ^ 4 / 4) * (h * Real.sqrt h) +
        (2 / 3 : ℝ) * L ^ 3 * (h * Real.sqrt h) := by
      linarith [mul_le_mul_of_nonneg_left h2 hA, mul_le_mul_of_nonneg_left h3 hB]
    _ = errorConstant L σ c₃ * h * Real.sqrt h := by unfold errorConstant; ring

theorem local_error_le_scale {L σ c₃ h e e₂ e₃ : ℝ}
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hc : 0 ≤ c₃) (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (he : e ≤ e₂ / 2 + e₃ / 6 + (h * σ ^ 2) ^ 2 / 4)
    (he₂ : e₂ ≤ 2 * (L * h) * (σ * Real.sqrt h) + (L * h) ^ 2)
    (he₃ : e₃ ≤ 4 * (c₃ * σ ^ 3 * h * Real.sqrt h + (L * h) ^ 3)) :
    e ≤ errorConstant L σ c₃ * h * Real.sqrt h := by
  have hs := moment_error_le_scale hL hσ hc h0 h1
  linarith

end Problem336AdditiveD139.InnovationErrorScale

end

end OAI
