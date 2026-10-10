import OAI.NumberTheory.Ostmann.Arithmetic.ScaleBudget
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimatePivotHeightBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsActual

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale

theorem pivot_exponent_bound_eventually (k : ℕ) (c β : ℝ) (hβ : -1 < β) :
    ∀ᶠ L : ℝ in atTop,
      (2*Real.exp (2*((1/10000:ℝ)*k)))*Real.exp (β*L) +
        (6/c + sourceAtomWidth k c) ≤ Real.exp ((β+1)*L) := by
  have h₁ := Arithmetic.ScaleBudget.eventually_poly_exp_le
    (2*Real.exp (2*((1/10000:ℝ)*k))) 0 (a := β) (b := β+1) (K := 1/2)
    (by linarith) (by norm_num)
  have h₂ := Arithmetic.ScaleBudget.eventually_poly_exp_le
    (6/c + sourceAtomWidth k c) 0 (a := 0) (b := β+1) (K := 1/2)
    (by linarith) (by norm_num)
  filter_upwards [h₁,h₂] with L hL₁ hL₂
  simp only [pow_zero, mul_one, zero_mul, Real.exp_zero] at hL₁ hL₂
  linarith

theorem sourcePivotRanges_height_eventually (k : ℕ) (c β : ℝ) (hβ : -1 < β) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (d : Decomposition) (E : Finset ℕ) (δ α ρ γ c₀ BD : ℝ)
        (s : SelectedWordSource d E δ L k α β ρ γ c₀)
        (w : FixedConfigurationWitness s c BD) (j : ℕ), j < k →
        ∀ P ∈ sourcePivotRanges w j,
          |(P : ℝ)| ≤ Real.exp (Real.exp ((β+1)*L)) := by
  filter_upwards [pivot_exponent_bound_eventually k c β hβ] with L hL
  intro d E δ α ρ γ c₀ BD s w j hj P hP
  rw [abs_of_nonneg (by exact_mod_cast P.pos.le)]
  exact (sourcePivotRanges_le_exp w j hj hP).trans (Real.exp_le_exp.mpr hL)

theorem sourceTemplatePivotRanges_height_eventually (k : ℕ) (c β : ℝ) (hβ : -1 < β) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (d : Decomposition) (E : Finset ℕ) (δ α ρ γ c₀ BD : ℝ)
        (s : SelectedWordSource d E δ L k α β ρ γ c₀)
        (w : FixedConfigurationWitness s c BD) (j : ℕ), j < k →
        ∀ P ∈ HigherBiasSource.SourceTemplate.sourcePivotRanges
          w.configuration s.J (gapSchedule BD k L) c j,
          |(P : ℝ)| ≤ Real.exp (Real.exp ((β+1)*L)) := by
  filter_upwards [sourcePivotRanges_height_eventually k c β hβ] with L hL
  exact hL

end Ostmann.Characters.DiagonalEstimate

end

end OAI
