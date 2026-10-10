import Mathlib

namespace OAI

noncomputable section
namespace AngularAperture

def transverse (y : ℝ) : ℝ := y ^ 2 / 4 + y ^ 4

def profile (q : ℝ) : ℝ := (q ^ 2 + q ^ 4) / 16

def level (τ η q s : ℝ) : ℝ := s - 1 / 2 - τ ^ 2 * (transverse (q * s) + η)

def aperture (τ η b q : ℝ) : Set ℝ :=
  {s | 0 ≤ s ∧ s ≤ b ∧ s ≤ 1 / 2 + τ ^ 2 * (transverse (q * s) + η)}

end AngularAperture

end

end OAI
