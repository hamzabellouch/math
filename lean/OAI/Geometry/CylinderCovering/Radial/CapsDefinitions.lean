import Mathlib

namespace OAI

noncomputable section
namespace CylinderCovering.RadialCaps

def G (r : ℝ) : ℝ := (1 + r ^ 2) / 2

def H (r : ℝ) : ℝ := (r ^ 2 + r ^ 4) / 2

def D0 (r : ℝ) : ℝ := G r ^ 2 + 2 * r ^ 2

def linearCap (β ε r : ℝ) : ℝ := 1 + ε ^ 2 * (H r + β)

def cubicCap (c ε r : ℝ) : ℝ := 1 + ε ^ 2 * H r + c * ε ^ 3

def fractionalCap (c ε r : ℝ) : ℝ := 1 + ε ^ 2 * H r + c * ε ^ (5 / 2 : ℝ)

def sqrtCap (β ε r : ℝ) : ℝ := Real.sqrt (1 + 2 * ε ^ 2 * (H r + β))

def Q (R : ℝ → ℝ) (ε : ℝ) : ℝ :=
  ∫ r in (-1 : ℝ)..1, R r ^ 2 / (2 * Real.sqrt (1 + ε ^ 2 * D0 r))

end CylinderCovering.RadialCaps

end

end OAI
