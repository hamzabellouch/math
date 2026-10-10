import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OAI.NumberTheory.Ostmann.Construction.HistorySmoothFactor

namespace OAI

/-! # Frequency support forced by the actual leaf Fourier factor -/

namespace Ostmann

open Filter

theorem archimedeanLeaf_frequency_le (X M s cutoff Δ C K : ℝ) (ψhat : ℝ → ℂ)
    (hX : 0 < X) (hM : 0 < M) (hupper : M ≤ X * Real.exp (Δ + C))
    (hsupport : ∀ t, ψhat t ≠ 0 → |t| ≤ Real.exp K)
    (hne : archimedeanLeafFactor X M s cutoff ψhat ≠ 0) :
    |s| ≤ Real.exp (Δ + C + K) := by
  have hψ : ψhat (-s * X / M) ≠ 0 := by
    intro hz
    apply hne
    simp only [archimedeanLeafFactor, hz, mul_zero]
  have harg := hsupport _ hψ
  rw [abs_div, abs_mul, abs_neg, abs_of_pos hX, abs_of_pos hM] at harg
  have harg' := (div_le_iff₀ hM).mp harg
  apply (mul_le_mul_iff_left₀ hX).mp
  calc
    |s| * X ≤ Real.exp K * M := harg'
    _ ≤ Real.exp K * (X * Real.exp (Δ + C)) :=
      mul_le_mul_of_nonneg_left hupper (Real.exp_pos _).le
    _ = Real.exp (Δ + C + K) * X := by
      simp only [Real.exp_add]
      ring

/-- The square-root margin in E_0 eventually covers the fixed Fourier
support radius and all bounded errors in the leaf modulus. -/
theorem archimedeanLeaf_frequency_window (C K : ℝ) :
    ∀ᶠ m : ℝ in atTop, ∀ X M s cutoff Δ : ℝ, ∀ ψhat : ℝ → ℂ,
      0 < X → 0 < M → M ≤ X * Real.exp (Δ + C) →
      (∀ t, ψhat t ≠ 0 → |t| ≤ Real.exp K) →
      archimedeanLeafFactor X M s cutoff ψhat ≠ 0 →
      |s| ≤ Real.exp (Δ + Real.sqrt m) := by
  filter_upwards [eventually_ge_atTop ((C + K) ^ 2)] with m hm
  intro X M s cutoff Δ ψhat hX hM hupper hsupport hne
  have hsqrt : C + K ≤ Real.sqrt m := Real.le_sqrt_of_sq_le hm
  apply (archimedeanLeaf_frequency_le X M s cutoff Δ C K ψhat hX hM hupper hsupport hne).trans
  apply Real.exp_le_exp.mpr
  linarith

end Ostmann

end OAI
