import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogDecay

namespace OAI

/-! # Uniform integral bounds for the actual logarithmic cutoff -/

namespace Ostmann

open MeasureTheory LineDeriv
open scoped SchwartzMap

 theorem quadratic_log_window_norm_bound (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X →
      (∫ u : ℝ, ‖quadraticLogWindow ρ X u‖) ≤ C / X ^ A := by
  refine ⟨quadraticLogDecayConstant ρ A * (∫ u : ℝ, ‖quadraticSmoothLogCutoff u‖),
    mul_nonneg (quadraticLogDecayConstant_nonneg ρ A) (integral_nonneg (fun _ => norm_nonneg _)), ?_⟩
  intro X hX
  have hh := quadratic_log_product_integral quadraticSmoothLogCutoff ρ A
    quadraticSmoothLogCutoff_support hX
  calc
    _ = ∫ u : ℝ, ‖quadraticSmoothLogCutoff u * ρ (X * Real.exp (-u))‖ := rfl
    _ ≤ _ := hh
    _ = _ := by ring

 theorem quadratic_log_window_second_norm_bound (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X →
      (∫ u : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (quadraticLogWindow ρ X))) u‖) ≤
        C / X ^ A := by
  let B := quadraticSmoothLogCutoff
  let B₁ := SchwartzMap.derivCLM ℂ ℂ B
  let B₂ := SchwartzMap.derivCLM ℂ ℂ B₁
  let ρ₁ := quadraticEulerDerivative ρ
  let ρ₂ := quadraticEulerDerivative ρ₁
  let C₀ := quadraticLogDecayConstant ρ A
  let C₁ := quadraticLogDecayConstant ρ₁ A
  let C₂ := quadraticLogDecayConstant ρ₂ A
  let I₀ := ∫ u : ℝ, ‖B u‖
  let I₁ := ∫ u : ℝ, ‖B₁ u‖
  let I₂ := ∫ u : ℝ, ‖B₂ u‖
  have hC₀ : 0 ≤ C₀ := quadraticLogDecayConstant_nonneg _ _
  have hC₁ : 0 ≤ C₁ := quadraticLogDecayConstant_nonneg _ _
  have hC₂ : 0 ≤ C₂ := quadraticLogDecayConstant_nonneg _ _
  have hI₀ : 0 ≤ I₀ := integral_nonneg (fun _ => norm_nonneg _)
  have hI₁ : 0 ≤ I₁ := integral_nonneg (fun _ => norm_nonneg _)
  have hI₂ : 0 ≤ I₂ := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨C₀ * I₂ + 2 * C₁ * I₁ + C₂ * I₀, by positivity, ?_⟩
  intro X hX
  let G₀ := fun u : ℝ => (C₀ / X ^ A) * ‖B₂ u‖
  let G₁ := fun u : ℝ => (C₁ / X ^ A) * ‖B₁ u‖
  let G₂ := fun u : ℝ => (C₂ / X ^ A) * ‖B u‖
  have hG₀ : Integrable G₀ := B₂.integrable.norm.const_mul _
  have hG₁ : Integrable G₁ := B₁.integrable.norm.const_mul _
  have hG₂ : Integrable G₂ := B.integrable.norm.const_mul _
  have hb (u : ℝ) :
      ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (quadraticLogWindow ρ X))) u‖ ≤
        G₀ u + 2 * G₁ u + G₂ u := by
    have h₀ := quadratic_log_product_decay B₂ ρ A quadraticSmoothLogCutoff_second_support hX u
    have h₁ := quadratic_log_product_decay B₁ ρ₁ A quadraticSmoothLogCutoff_deriv_support hX u
    have h₂ := quadratic_log_product_decay B ρ₂ A quadraticSmoothLogCutoff_support hX u
    rw [quadraticLogWindow_second]
    change ‖B₂ u * ρ (X * Real.exp (-u)) - 2 * B₁ u * ρ₁ (X * Real.exp (-u)) +
      B u * ρ₂ (X * Real.exp (-u))‖ ≤ _
    calc
      _ ≤ ‖B₂ u * ρ (X * Real.exp (-u)) - 2 * B₁ u * ρ₁ (X * Real.exp (-u))‖ +
          ‖B u * ρ₂ (X * Real.exp (-u))‖ := norm_add_le _ _
      _ ≤ (‖B₂ u * ρ (X * Real.exp (-u))‖ +
          ‖2 * B₁ u * ρ₁ (X * Real.exp (-u))‖) +
          ‖B u * ρ₂ (X * Real.exp (-u))‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖B₂ u * ρ (X * Real.exp (-u))‖ +
          2 * ‖B₁ u * ρ₁ (X * Real.exp (-u))‖ +
          ‖B u * ρ₂ (X * Real.exp (-u))‖ := by
        norm_num [mul_assoc, norm_mul]
      _ ≤ _ := add_le_add (add_le_add h₀ (mul_le_mul_of_nonneg_left h₁ (by norm_num))) h₂
  calc
    _ ≤ ∫ u : ℝ, G₀ u + 2 * G₁ u + G₂ u :=
      integral_mono (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (quadraticLogWindow ρ X))).integrable.norm
        ((hG₀.add (hG₁.const_mul 2)).add hG₂) hb
    _ = (C₀ / X ^ A) * I₂ + 2 * ((C₁ / X ^ A) * I₁) + (C₂ / X ^ A) * I₀ := by
      rw [integral_add (f := fun u => G₀ u + 2 * G₁ u) (g := G₂)
        (hG₀.add (hG₁.const_mul 2)) hG₂,
        integral_add (f := G₀) (g := fun u => 2 * G₁ u) hG₀ (hG₁.const_mul 2)]
      simp only [G₀, G₁, G₂, integral_const_mul, I₀, I₁, I₂]
    _ = _ := by ring

end Ostmann

end OAI
