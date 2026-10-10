import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Absorbing a dominated finite sampling law into a complex multiplier -/

namespace Ostmann

noncomputable def finitePriorDensity {X : Type*} (μ : X → ℝ) (F : X → ℂ) (x : X) : ℂ :=
  F x / (μ x : ℂ)

/-- The scalar is the retained product of one-over-prime line probabilities.
It is positive, so a zero dominating prior forces the original summand to vanish. -/
theorem finitePriorDensity_cancel {X : Type*} (μ : X → ℝ) (F : X → ℂ)
    (c : X → ℝ) (B : ℝ) (hc : ∀ x, 0 < c x)
    (hbound : ∀ x, ‖F x‖ * c x ≤ B * μ x) (x : X) :
    (μ x : ℂ) * finitePriorDensity μ F x = F x := by
  by_cases hμ : μ x = 0
  · have hF : F x = 0 := by
      apply norm_eq_zero.mp
      have h := hbound x
      rw [hμ, mul_zero] at h
      have hp := hc x
      exact le_antisymm (by nlinarith [norm_nonneg (F x)]) (norm_nonneg _)
    simp only [finitePriorDensity, hμ, hF, Complex.ofReal_zero, zero_div, mul_zero]
  · unfold finitePriorDensity
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hμ)

theorem finitePriorDensity_bound {X : Type*} (μ : X → ℝ) (F : X → ℂ)
    (c : X → ℝ) (B : ℝ) (hμ : ∀ x, 0 ≤ μ x) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖F x‖ * c x ≤ B * μ x) (x : X) :
    ‖finitePriorDensity μ F x‖ * c x ≤ B := by
  by_cases hz : μ x = 0
  · simp only [finitePriorDensity, hz, Complex.ofReal_zero, div_zero, norm_zero, zero_mul]
    exact hB
  · have hp : 0 < μ x := lt_of_le_of_ne (hμ x) (Ne.symm hz)
    simp only [finitePriorDensity, norm_div, Complex.norm_real, Real.norm_of_nonneg (hμ x)]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hp).mpr (hbound x)

theorem finitePriorDensity_ne_zero {X : Type*} (μ : X → ℝ) (F : X → ℂ)
    (x : X) (h : finitePriorDensity μ F x ≠ 0) : F x ≠ 0 := by
  intro hF
  apply h
  simp only [finitePriorDensity, hF, zero_div]

end Ostmann

end OAI
