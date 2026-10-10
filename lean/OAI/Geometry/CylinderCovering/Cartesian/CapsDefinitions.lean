import Mathlib

namespace OAI

noncomputable section

namespace CylinderCovering.CartesianCaps

def D (y : ℝ) : ℝ := y ^ 2 / 4 + y ^ 4

def d (q : ℝ) : ℝ := (q ^ 2 + q ^ 4) / 16

def residual (τ η q s : ℝ) : ℝ := s - 1 / 2 - τ ^ 2 * (D (q * s) + η)

def aperture (τ η b q : ℝ) : Set ℝ :=
  {s | 0 ≤ s ∧ s ≤ b ∧ s ≤ 1 / 2 + τ ^ 2 * (D (q * s) + η)}

def cap (τ η q : ℝ) : ℝ := by
  classical
  exact if h : ∃ s : ℝ, s ∈ Set.Icc (1 / 2 : ℝ) (3 / 4) ∧ residual τ η q s = 0 then
    Classical.choose h
  else 1 / 2

end CylinderCovering.CartesianCaps

end

end OAI
