import Mathlib

namespace OAI

noncomputable section

namespace Problem310

def dyadicPoint (n : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ n

theorem dyadic_affine_avoidance :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧
      MeasureTheory.volume E > ENNReal.ofReal (1 - η) ∧
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
        x + s * dyadicPoint n ∉ E := by
  sorry

end Problem310

end

end OAI
