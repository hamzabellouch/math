import OAI.Geometry.CylinderCovering.Radial.CapsDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.OrthonormalHeight

def k : ℝ := 1 / Real.sqrt 2

def upperHeight (τ y z q : ℝ) : ℝ := 1 / k - z + τ * y * q
def lowerHeight (τ x z p : ℝ) : ℝ := 1 / k + z - τ * x * p
def cap (τ r : ℝ) : ℝ := 1 / k + τ ^ 2 * k * RadialCaps.H r + 10 * τ ^ 3

def RootEquations (τ x y z p q : ℝ) : Prop :=
  x = (1 - k * z) * q - (k * τ) * y * (1 - q ^ 2) / 2 ∧
  y = (1 + k * z) * p + (k * τ) * x * (1 - p ^ 2) / 2

def ErrorStatement : Prop :=
  ∀ τ x y z p q : ℝ, 0 < τ → |x| ≤ 2 → |y| ≤ 2 →
    |p| ≤ 1 → |q| ≤ 1 → RootEquations τ x y z p q →
    1 / k < upperHeight τ y z q → 1 / k < lowerHeight τ x z p →
    τ * (y * q - x * p) ≤
      k * τ ^ 2 * (RadialCaps.H p + RadialCaps.H q) + 9 * k ^ 2 * τ ^ 3

def CoverageStatement : Prop :=
  ∀ τ x y z : ℝ, 0 < τ → |x| ≤ 1 - k * z → |y| ≤ 1 + k * z →
    (∃ q u : ℝ, |q| ≤ 1 ∧ 0 ≤ u ∧ u ≤ cap τ q ∧
      x = k * (u * q - τ * y * RadialCaps.G q) ∧
      z = 1 / k - u + τ * y * q) ∨
    (∃ p v : ℝ, |p| ≤ 1 ∧ 0 ≤ v ∧ v ≤ cap τ p ∧
      y = k * (v * p + τ * x * RadialCaps.G p) ∧
      z = -1 / k + v + τ * x * p)

def Statement : Prop := ErrorStatement ∧ CoverageStatement

end CylinderCovering.OrthonormalHeight

end

end OAI
