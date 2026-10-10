import Mathlib

namespace OAI

noncomputable section
namespace RadialPhysical

abbrev Space := EuclideanSpace ℝ (Fin 3)

def height (b : ℝ) : ℝ := Real.sqrt 2 * b

def point (b x y t : ℝ) : Space := !₂[x, y, height b * t]

def canonicalPoint (X Y Z : ℝ) : Space := !₂[X, Y, Real.sqrt 2 * Z]

def tetrahedron (b : ℝ) : Set Space :=
  {z | ∃ x y t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ |x| ≤ b * t ∧
      |y| ≤ b * (1 - t) ∧ z = point b x y t}

def effectiveTilt (b eta : ℝ) : ℝ := eta * b ^ 2

def capPolynomial (b beta s : ℝ) : ℝ :=
  (s ^ 4 + b ^ 2 * s ^ 2) / 4 + b ^ 4 * beta / 2

def linearCap (b eta beta s : ℝ) : ℝ := 1 / 2 + eta ^ 2 * capPolynomial b beta s

def squareCap (b eta beta s : ℝ) : ℝ := Real.sqrt (1 / 4 + eta ^ 2 * capPolynomial b beta s)

def canonicalProfile (r : ℝ) : ℝ := (r ^ 4 + r ^ 2) / 2

def canonicalSpeed (r : ℝ) : ℝ := (1 + r ^ 2) ^ 2 / 4 + 2 * r ^ 2

def canonicalCost (eps : ℝ) (R : ℝ → ℝ) : ℝ :=
  ∫ r in (-1 : ℝ)..1, R r ^ 2 / (2 * Real.sqrt (1 + eps ^ 2 * canonicalSpeed r))

def scaledDensity (b eta : ℝ) (T : ℝ → ℝ) (s : ℝ) : ℝ :=
  T s ^ 2 / Real.sqrt (1 + eta ^ 2 * ((s ^ 2 + b ^ 2) ^ 2 / 4 + height b ^ 2 * s ^ 2))

def scaledCost (b eta : ℝ) (T : ℝ → ℝ) : ℝ :=
  height b * ∫ s in -b..b, scaledDensity b eta T s

def mapToCanonical (b : ℝ) (z : Space) : Space :=
  (2 / b) • z - !₂[0, 0, Real.sqrt 2]

def relativeQuadraticTerm (b eta beta : ℝ) : ℝ :=
  (2 * beta - 1 / 30) * effectiveTilt b eta ^ 2

def nonorthPoint (p q t : ℝ) : Space :=
  !₂[p / Real.sqrt 2, q / Real.sqrt 2, t]

def centeredLinearCap (b eta beta s : ℝ) : ℝ :=
  1 + eta ^ 2 * ((s ^ 4 + b ^ 2 * s ^ 2) / 2 + b ^ 4 * beta)

def quadraticCost (b eta beta : ℝ) : ℝ :=
  b * height b / 2 * (1 + relativeQuadraticTerm b eta beta)

def centeredTetrahedron (b : ℝ) : Set Space :=
  {z | ∃ x y t : ℝ, -1 ≤ t ∧ t ≤ 1 ∧ |x| ≤ b * (1 + t) ∧
      |y| ≤ b * (1 - t) ∧ z = point b x y t}

def mapCenteredToCanonical (b : ℝ) (z : Space) : Space := (1 / b) • z

end RadialPhysical

end

end OAI
