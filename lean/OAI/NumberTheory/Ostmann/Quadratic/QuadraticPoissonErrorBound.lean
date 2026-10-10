import OAI.NumberTheory.Ostmann.Quadratic.QuadraticTruncatedPoisson

namespace OAI

/-! # Quantitative error of the actual truncated coprime Poisson formula -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

 theorem quadratic_poisson_error_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, ∀ X U V : ℝ, 0 < X → 0 < U → 0 < V → ∀ L : ℕ,
      ‖quadraticPoissonError q ψ X U V L‖ ≤
        C * (U * (U / X) ^ (A + 1) + X * (X / V) ^ (A + 1) +
          V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) := by
  obtain ⟨C₁, hC₁, hc₁⟩ := quadratic_small_divisor_tail ψ A
  obtain ⟨C₂, hC₂, hc₂⟩ := quadratic_large_divisor_tail ψ A
  obtain ⟨C₃, hC₃, hc₃⟩ := quadratic_middle_frequency_tail ψ A
  refine ⟨C₁ + C₂ + C₃, by positivity, ?_⟩
  intro q X U V hX hU hV L
  have h₁ := hc₁ q X U hX hU
  have h₂ := hc₂ q X V hX hV
  have h₃ := hc₃ q X U V hX hV L
  have hh : ‖quadraticPoissonError q ψ X U V L‖ ≤
      C₁ * U * (U / X) ^ (A + 1) + C₂ * X * (X / V) ^ (A + 1) +
        C₃ * V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A := by
    unfold quadraticPoissonError
    apply (norm_add_le _ _).trans
    apply add_le_add _ h₃
    exact (norm_add_le _ _).trans (add_le_add h₁ h₂)
  apply hh.trans
  calc
    _ = C₁ * (U * (U / X) ^ (A + 1)) + C₂ * (X * (X / V) ^ (A + 1)) +
        C₃ * (V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) := by ring
    _ ≤ (C₁ + C₂ + C₃) * (U * (U / X) ^ (A + 1)) +
        (C₁ + C₂ + C₃) * (X * (X / V) ^ (A + 1)) +
        (C₁ + C₂ + C₃) * (V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) := by gcongr <;> linarith
    _ = _ := by ring

 theorem quadratic_truncated_poisson_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, [NeZero q] → q ≠ 1 →
      ∀ X U V : ℝ, 0 < X → 0 < U → U ≤ V → ∀ L : ℕ,
      ‖(∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) -
        quadraticPoissonCore q ψ X U V L‖ ≤
      C * (U * (U / X) ^ (A + 1) + X * (X / V) ^ (A + 1) +
        V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_poisson_error_bound ψ A
  refine ⟨C, hC, ?_⟩
  intro q _ hq1 X U V hX hU hUV L
  rw [quadratic_truncated_coprime_poisson hq1 ψ hX hUV L, add_sub_cancel_left]
  exact hc q X U V hX hU (hU.trans_le hUV) L

end Ostmann

end OAI
