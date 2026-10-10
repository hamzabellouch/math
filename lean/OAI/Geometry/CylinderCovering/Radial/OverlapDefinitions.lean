import OAI.Geometry.CylinderCovering.Radial.CapsDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.RadialOverlap

def RootEquations (ε x y t p q : ℝ) : Prop :=
  y = (1 - t) * q - ε * x * (1 - q ^ 2) / 2 ∧
  x = (1 + t) * p + ε * y * (1 - p ^ 2) / 2

def rho (ε x t q : ℝ) : ℝ := 1 - t + ε * x * q

def sigma (ε y t p : ℝ) : ℝ := 1 + t - ε * y * p

def T (ε x t q : ℝ) : ℝ := t - ε * x * q

def S (ε y t p : ℝ) : ℝ := -t + ε * y * p

def IdentitiesStatement : Prop :=
  ∀ ε x y t p q : ℝ, RootEquations ε x y t p q →
    ((1 + ε * p * q) * rho ε x t q + (1 - ε * p * q) * sigma ε y t p =
      2 + ε ^ 2 * (q * RadialCaps.G p * y + p * RadialCaps.G q * x)) ∧
    ((1 + ε * x * q) * T ε x t q = t - ε * x * y - ε ^ 2 * x ^ 2 * RadialCaps.G q) ∧
    ((1 - ε * y * p) * S ε y t p = -t + ε * x * y - ε ^ 2 * y ^ 2 * RadialCaps.G p) ∧
    ((rho ε x t q) ^ 2 = (1 - t) ^ 2 + 2 * ε * x * y + ε ^ 2 * x ^ 2) ∧
    ((sigma ε y t p) ^ 2 = (1 + t) ^ 2 - 2 * ε * x * y + ε ^ 2 * y ^ 2)

def ComplementaryBoundStatement : Prop :=
  ∀ ε x y t p q : ℝ, 0 < ε → ε ≤ 1 / 4 →
    |x| ≤ 2 → |y| ≤ 2 → |p| ≤ 1 → |q| ≤ 1 →
    RootEquations ε x y t p q → T ε x t q ≤ 0 → S ε y t p ≤ 0 →
    |T ε x t q| ≤ 16 * ε ^ 2 ∧ |S ε y t p| ≤ 16 * ε ^ 2

end CylinderCovering.RadialOverlap

end

end OAI
