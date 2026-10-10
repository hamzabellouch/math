import Mathlib

namespace OAI

noncomputable section

namespace CylinderCovering.RadialTriangle

def region (l r m d : ℝ) : Set (ℝ × ℝ) :=
  {p | l ≤ p.1 ∧ p.1 ≤ r ∧ |p.2 - m * p.1| ≤ d / 2 * (p.1 - l)}

def vertices (l r m d : ℝ) : Fin 3 → ℝ × ℝ :=
  ![(l, m * l), (r, m * r - d / 2 * (r-l)), (r, m * r + d / 2 * (r-l))]

def collar (A B : ℝ) : ℝ := 2 * (A + B) + 1

def freezingRegion (A B R m d : ℝ) : Set (ℝ × ℝ) :=
  region (-(collar A B) * d) (R + A * d) m d

end CylinderCovering.RadialTriangle

end

end OAI
