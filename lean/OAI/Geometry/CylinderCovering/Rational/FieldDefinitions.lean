import Mathlib

namespace OAI

noncomputable section

namespace SlopeRational

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def vec2 (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

def radius (T : ℝ) : ℝ := 1 / 2 - T

def potential (d Y T : ℝ) : ℝ :=
  (Y ^ 2 - radius T ^ 2 / 4) / (4 * (radius T + d))

def a (d Y T : ℝ) : ℝ :=
  -Y ^ 2 / (4 * (radius T + d) ^ 2) -
    radius T * (radius T + 2 * d) / (16 * (radius T + d) ^ 2)

def b (d Y T : ℝ) : ℝ := Y / (2 * (radius T + d))

def field (d : ℝ) (z : Plane) : Plane := vec2 (a d (z 0) (z 1)) (b d (z 0) (z 1))

def wedge : Set Plane := {z | 2 * |z 0| ≤ radius (z 1)}

def alpha (d : ℝ) : ℝ := 1 / (1 + 2 * d)

def ceilingConstant (d : ℝ) : ℝ :=
  ((1 / 2 : ℝ) * (1 / 2 + 2 * d)) / (16 * (1 / 2 + d) ^ 2)

def ceilingQuadratic (d : ℝ) : ℝ := 1 / (4 * (1 / 2 + d) ^ 2)

def ceilingCoefficient (d Y : ℝ) : ℝ := ceilingConstant d + ceilingQuadratic d * Y ^ 2

def ceilingPolynomial (d Y : ℝ) : ℝ := alpha d * ceilingCoefficient d Y * Y ^ 2

def labelDomain (d ε q : ℝ) : Set Plane :=
  {z | z ∈ wedge ∧ -(1 / 4 : ℝ) ≤ z 1 ∧
    -ε ^ 2 * ceilingPolynomial d (z 0) - q ≤ z 1}

end SlopeRational

end

end OAI
