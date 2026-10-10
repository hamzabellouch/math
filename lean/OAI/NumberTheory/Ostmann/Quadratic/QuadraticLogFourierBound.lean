import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogNormBounds

namespace OAI

/-! # Uniform Fourier cost of the concrete Poisson weight -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

 theorem quadratic_log_window_fourier_decay (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X →
      (∫ u : ℝ, ‖𝓕 (quadraticLogWindow ρ X) u‖) ≤ C / X ^ A := by
  obtain ⟨C₀, hC₀, h₀⟩ := quadratic_log_window_norm_bound ρ A
  obtain ⟨C₂, hC₂, h₂⟩ := quadratic_log_window_second_norm_bound ρ A
  let J := ∫ u : ℝ, (1 + ‖u‖) ^ (-(2 : ℝ))
  have hJ : 0 ≤ J := integral_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)
  have hp : 0 < (2 * Real.pi) ^ 2 := by positivity
  refine ⟨2 * (C₀ + C₂ / (2 * Real.pi) ^ 2) * J, by positivity, ?_⟩
  intro X hX
  calc
    _ ≤ 2 * ((∫ u : ℝ, ‖quadraticLogWindow ρ X u‖) +
        (∫ u : ℝ, ‖(LineDeriv.lineDerivOp (1 : ℝ)
          (LineDeriv.lineDerivOp (1 : ℝ) (quadraticLogWindow ρ X))) u‖) /
          (2 * Real.pi) ^ 2) * J := quadratic_fourier_l1_bound _
    _ ≤ 2 * (C₀ / X ^ A + (C₂ / X ^ A) / (2 * Real.pi) ^ 2) * J := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (h₀ X hX)
          (div_le_div_of_nonneg_right (h₂ X hX) hp.le)) (by norm_num)) hJ
    _ = _ := by ring

 theorem quadratic_log_window_fourier_min (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X →
      (∫ u : ℝ, ‖𝓕 (quadraticLogWindow ρ X) u‖) ≤ C * min 1 (1 / X ^ A) := by
  obtain ⟨C₀, hC₀, h₀⟩ := quadratic_log_window_fourier_decay ρ 0
  obtain ⟨C₁, hC₁, h₁⟩ := quadratic_log_window_fourier_decay ρ A
  refine ⟨max C₀ C₁, le_max_of_le_left hC₀, ?_⟩
  intro X hX
  rw [mul_min_of_nonneg _ _ (le_max_of_le_left hC₀), mul_one,
    mul_one_div]
  apply le_min
  · have hh : (∫ u : ℝ, ‖𝓕 (quadraticLogWindow ρ X) u‖) ≤ C₀ := by
      simpa using h₀ X hX
    exact hh.trans (le_max_left _ _)
  · exact (h₁ X hX).trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))

 theorem quadratic_log_kernel_fourier_bound (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X → ∀ N : ℕ, 0 < N →
      (∫ u : ℝ, ‖𝓕 (quadraticLogKernel ρ X N) u‖) ≤
        C * min 1 (((N : ℝ) ^ 2 / X) ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_log_window_fourier_min ρ A
  refine ⟨C, hC, ?_⟩
  intro X hX N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [quadraticLogKernel_fourier_cost]
  have hh := hc (X / (N : ℝ) ^ 2) (by positivity)
  have he : 1 / (X / (N : ℝ) ^ 2) ^ A = ((N : ℝ) ^ 2 / X) ^ A := by
    rw [one_div, div_pow, inv_div, div_pow]
  simpa only [he] using hh

end Ostmann

end OAI
