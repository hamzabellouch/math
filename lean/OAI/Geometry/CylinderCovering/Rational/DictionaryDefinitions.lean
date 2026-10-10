import OAI.Geometry.CylinderCovering.Rational.FieldDefinitions
import OAI.Geometry.CylinderCovering.Rational.SimilarityDefinitions

namespace OAI

noncomputable section
namespace RationalDictionary

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)

def vec2 (x y : ℝ) : Plane := !₂[x, y]
def vec3 (x y z : ℝ) : Space := !₂[x, y, z]

def c0 : ℝ := 1 / Real.sqrt 2

def ell : ℝ := 1 / (2 * Real.sqrt 2)

def g (d0 s : ℝ) : ℝ := (1 + d0) / (s + d0)

def gPrime (d0 s : ℝ) : ℝ := -(1 + d0) / (s + d0) ^ 2

def v1 (d0 u s : ℝ) : ℝ :=
  c0 ^ 2 * s * g d0 s + (1 / 2) * (c0 ^ 2 * s ^ 2 - u ^ 2) * gPrime d0 s

def v2 (d0 u s : ℝ) : ℝ := u * g d0 s

def velocity (d0 : ℝ) (p : Plane) : Plane := vec2 (v1 d0 (p 0) (p 1)) (v2 d0 (p 0) (p 1))

def A0 (d0 : ℝ) : ℝ := c0 ^ 2 * (1 - 1 / (2 * (1 + d0)))

def B0 (d0 : ℝ) : ℝ := 1 / (2 * (1 + d0))

def a0 (d0 u : ℝ) : ℝ := A0 d0 * u ^ 2 + B0 d0 * u ^ 4

def uncenteredDomain (d0 eta0 k : ℝ) : Set Plane :=
  {p | 0 ≤ p 1 ∧ p 1 ≤ 3 / 2 ∧ |p 0| ≤ c0 * p 1 ∧
    p 1 ≤ 1 + k ^ 2 * (a0 d0 (p 0) + eta0)}

def labelMap (p : Plane) : Plane := vec2 (ell * p 0) ((1 - p 1) / 2)

def centeredRegularization (d0 : ℝ) : ℝ := d0 / 2

def centeredTilt (d0 k : ℝ) : ℝ := 4 * (1 + d0) * k

def centeredPadding (eta0 k : ℝ) : ℝ := eta0 * k ^ 2 / 2

def centeredMargin (d0 eta0 : ℝ) : ℝ := eta0 / (32 * (1 + d0) ^ 2)

def lineMap (d0 k r : ℝ) (p : Plane) : Plane := p + (r * k) • velocity d0 p

def inverseLabelMap (p : Plane) : Plane := vec2 (p 0 / ell) (1 - 2 * p 1)

def reflectLabel (p : Plane) : Plane := vec2 (-p 0) (p 1)

def uncenteredFirstSweep (d0 eta0 k : ℝ) : Set Space :=
  {z | ∃ p ∈ uncenteredDomain d0 eta0 k, ∃ r : ℝ, |r| ≤ 2 * c0 ∧
    z = vec3 r (lineMap d0 k r p 0) (lineMap d0 k r p 1)}

def uncenteredSecondSweep (d0 eta0 k : ℝ) : Set Space :=
  {z | ∃ p ∈ uncenteredDomain d0 eta0 k, ∃ r : ℝ, |r| ≤ 2 * c0 ∧
    z = vec3 (lineMap d0 k (-r) p 0) r (2 - lineMap d0 k (-r) p 1)}

def centeredFirstPoint (d eps x : ℝ) (p : Plane) : Space :=
  vec3 x (p 0 + eps * x * SlopeRational.a d (p 0) (p 1))
    (c0 * (p 1 + eps * x * SlopeRational.b d (p 0) (p 1)))

def centeredSecondPoint (d eps y : ℝ) (p : Plane) : Space :=
  vec3 (p 0 - eps * y * SlopeRational.a d (p 0) (p 1)) y
    (-c0 * (p 1 - eps * y * SlopeRational.b d (p 0) (p 1)))

def centeredFirstSweep (d eps q : ℝ) : Set Space :=
  {z | ∃ p ∈ SlopeRational.labelDomain d eps q, ∃ x : ℝ, |x| ≤ 1 / 2 ∧
    z = centeredFirstPoint d eps x p}

def centeredSecondSweep (d eps q : ℝ) : Set Space :=
  {z | ∃ p ∈ SlopeRational.labelDomain d eps q, ∃ y : ℝ, |y| ≤ 1 / 2 ∧
    z = centeredSecondPoint d eps y p}

def threshold (d0 k r u : ℝ) : ℝ :=
  1 + k * r * u + k ^ 2 * (a0 d0 u - r ^ 2 * v1 d0 u 1)

def uncenteredWeight (d0 k : ℝ) (p : Plane) : ℝ :=
  1 / Real.sqrt (1 + k ^ 2 * (v1 d0 (p 0) (p 1) ^ 2 + v2 d0 (p 0) (p 1) ^ 2))

def centeredWeight (d eps : ℝ) (p : Plane) : ℝ :=
  c0 / Real.sqrt (1 + eps ^ 2 *
    (SlopeRational.a d (p 0) (p 1) ^ 2 + c0 ^ 2 * SlopeRational.b d (p 0) (p 1) ^ 2))

def uncenteredCost (d0 eta0 k : ℝ) : ℝ :=
  ∫ p in uncenteredDomain d0 eta0 k, uncenteredWeight d0 k p

def centeredCost (d eps q : ℝ) : ℝ :=
  ∫ p in SlopeRational.labelDomain d eps q, centeredWeight d eps p

end RationalDictionary

end

end OAI
