import Mathlib

namespace OAI

noncomputable section

namespace CylinderCovering.Footprints

def quadraticIntercept (ε x q c ρ : ℝ) : ℝ × ℝ :=
  let u := ρ - ε * x * (q - c)
  (u, q * u + ε * x / 2 * (q - c) ^ 2)

def absoluteFootprint (m M d A B : ℝ) : Set (ℝ × ℝ) :=
  {p | -A * d ≤ p.1 ∧ p.1 ≤ M + A * d ∧
    |p.2 - m * p.1| ≤ d / 2 * |p.1| + B * d ^ 2}

def affineFootprint (c M d A B : ℝ) : Set (ℝ × ℝ) :=
  {p | -A * d ≤ p.1 ∧ p.1 ≤ M + A * d ∧
    |p.2 - c * p.1| ≤ d / 2 * p.1 + B * d ^ 2}

def endpointFootprint (c M d ε : ℝ) : Set (ℝ × ℝ) :=
  {p | -2 * ε * d ≤ p.1 ∧ p.1 ≤ M + 2 * ε * d ∧
    -3 * ε * d ^ 2 ≤ p.2 - c * p.1 ∧
    p.2 - c * p.1 ≤ d * p.1 + 3 * ε * d ^ 2}

def absoluteArea (M d A B : ℝ) : ℝ :=
  d * M ^ 2 / 2 + (A + 2 * B) * M * d ^ 2 +
    (A ^ 2 + 4 * A * B) * d ^ 3

def affineArea (M d A B : ℝ) : ℝ :=
  d * M ^ 2 / 2 + (A + 2 * B) * M * d ^ 2 + 4 * A * B * d ^ 3

end CylinderCovering.Footprints

end

end OAI
