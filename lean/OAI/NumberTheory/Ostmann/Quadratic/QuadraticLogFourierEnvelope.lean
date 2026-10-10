import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogFourierBound

namespace OAI

/-! # A common Fourier majorant for varying Poisson parameters -/

namespace Ostmann

open MeasureTheory LineDeriv
open scoped SchwartzMap FourierTransform

noncomputable def quadraticFourierEnvelope (u : ℝ) : ℝ := (1 + ‖u‖) ^ (-(2 : ℝ))

 theorem quadraticFourierEnvelope_nonneg (u : ℝ) : 0 ≤ quadraticFourierEnvelope u :=
  Real.rpow_nonneg (by positivity) _

 theorem quadraticFourierEnvelope_integrable : Integrable quadraticFourierEnvelope :=
  integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2)

 theorem quadratic_fourier_pointwise_bound (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ‖𝓕 f u‖ ≤ 2 * ((∫ x : ℝ, ‖f x‖) +
      (∫ x : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) x‖) / (2 * Real.pi) ^ 2) *
        quadraticFourierEnvelope u := by
  let A := ∫ x : ℝ, ‖f x‖
  let B := (∫ x : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) x‖) / (2 * Real.pi) ^ 2
  have h₀ := quadratic_fourier_norm_le_integral f u
  have h₂ := quadratic_fourier_frequency_bound f u
  have he : (1 + ‖u‖) ^ 2 ≤ 2 * (1 + u ^ 2) := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have hm := mul_le_mul_of_nonneg_right he (norm_nonneg (𝓕 f u))
  have hw : (1 + ‖u‖) ^ 2 * ‖𝓕 f u‖ ≤ 2 * (A + B) := by
    calc
      _ ≤ 2 * (1 + u ^ 2) * ‖𝓕 f u‖ := hm
      _ = 2 * (‖𝓕 f u‖ + u ^ 2 * ‖𝓕 f u‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h₀ h₂) (by norm_num)
  rw [quadraticFourierEnvelope, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖u‖),
    Real.rpow_two, ← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0 < (1 + ‖u‖) ^ 2)).mpr (by nlinarith [hw])

 theorem quadratic_log_window_envelope_decay (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X → ∀ u : ℝ,
      ‖𝓕 (quadraticLogWindow ρ X) u‖ ≤ (C / X ^ A) * quadraticFourierEnvelope u := by
  obtain ⟨C₀, hC₀, h₀⟩ := quadratic_log_window_norm_bound ρ A
  obtain ⟨C₂, hC₂, h₂⟩ := quadratic_log_window_second_norm_bound ρ A
  have hp : 0 < (2 * Real.pi) ^ 2 := by positivity
  refine ⟨2 * (C₀ + C₂ / (2 * Real.pi) ^ 2), by positivity, ?_⟩
  intro X hX u
  calc
    _ ≤ 2 * ((∫ x : ℝ, ‖quadraticLogWindow ρ X x‖) +
      (∫ x : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (quadraticLogWindow ρ X))) x‖) /
        (2 * Real.pi) ^ 2) * quadraticFourierEnvelope u := quadratic_fourier_pointwise_bound _ _
    _ ≤ 2 * (C₀ / X ^ A + (C₂ / X ^ A) / (2 * Real.pi) ^ 2) *
        quadraticFourierEnvelope u := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (h₀ X hX)
          (div_le_div_of_nonneg_right (h₂ X hX) hp.le)) (by norm_num))
        (quadraticFourierEnvelope_nonneg u)
    _ = _ := by ring

 theorem quadratic_log_window_envelope (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X → ∀ u : ℝ,
      ‖𝓕 (quadraticLogWindow ρ X) u‖ ≤
        C * min 1 (1 / X ^ A) * quadraticFourierEnvelope u := by
  obtain ⟨C₀, hC₀, h₀⟩ := quadratic_log_window_envelope_decay ρ 0
  obtain ⟨C₁, hC₁, h₁⟩ := quadratic_log_window_envelope_decay ρ A
  let C := max C₀ C₁
  have hC : 0 ≤ C := le_max_of_le_left hC₀
  refine ⟨C, hC, ?_⟩
  intro X hX u
  rw [mul_min_of_nonneg _ _ hC, min_mul_of_nonneg _ _ (quadraticFourierEnvelope_nonneg u),
    mul_one, mul_one_div]
  apply le_min
  · have hh : ‖𝓕 (quadraticLogWindow ρ X) u‖ ≤ C₀ * quadraticFourierEnvelope u := by
      simpa using h₀ X hX u
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (quadraticFourierEnvelope_nonneg u))
  · exact (h₁ X hX u).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
      (quadraticFourierEnvelope_nonneg u))

 theorem quadratic_log_kernel_envelope (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ X Y : ℝ, 0 < Y → Y ≤ X → ∀ u : ℝ,
      ‖𝓕 (quadraticLogKernel ρ X N) u‖ ≤
        C * min 1 (((N : ℝ) ^ 2 / Y) ^ A) * quadraticFourierEnvelope u := by
  obtain ⟨C, hC, hc⟩ := quadratic_log_window_envelope ρ A
  refine ⟨C, hC, ?_⟩
  intro N hN X Y hY hYX u
  have hX : 0 < X := hY.trans_le hYX
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [quadraticLogKernel, quadratic_fourier_translate_norm]
  have hh := hc (X / (N : ℝ) ^ 2) (by positivity) u
  have he : 1 / (X / (N : ℝ) ^ 2) ^ A = ((N : ℝ) ^ 2 / X) ^ A := by
    rw [one_div, div_pow, inv_div, div_pow]
  rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (quadraticFourierEnvelope_nonneg u)
  apply mul_le_mul_of_nonneg_left _ hC
  apply min_le_min_left
  gcongr

end Ostmann

end OAI
