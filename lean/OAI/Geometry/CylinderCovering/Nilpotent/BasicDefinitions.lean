import Mathlib

namespace OAI

namespace CylinderCovering.Nilpotent

noncomputable section

def v (p : ℝ) : ℝ := (1 + p ^ 2) / 4

def w (p : ℝ) : ℝ := p / 2

def a (p : ℝ) : ℝ := p ^ 2 * v p / 4

def height (k p : ℝ) : ℝ := 1 / 2 + k ^ 2 * a p + k ^ 3

def InTetrahedron (x y z : ℝ) : Prop :=
  0 ≤ z ∧ z ≤ 1 ∧ |x| ≤ 1 - z ∧ |y| ≤ z

def InLowerSweep (k x y z : ℝ) : Prop :=
  ∃ p t : ℝ, |x| ≤ 1 ∧ |p| ≤ 1 ∧ 0 ≤ t ∧ t ≤ height k p ∧
    y = p * t + k * x * v p ∧ z = t + k * x * w p

def InUpperSweep (k x y z : ℝ) : Prop :=
  ∃ p t : ℝ, |y| ≤ 1 ∧ |p| ≤ 1 ∧ 0 ≤ t ∧ t ≤ height k p ∧
    x = p * t - k * y * v p ∧ z = 1 - t + k * y * w p

end
end CylinderCovering.Nilpotent

end OAI
