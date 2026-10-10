import OAI.Geometry.CylinderCovering.Singular.EdgeOneDefinitions
import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
namespace SingularEdgeOne

def edgeDomain0 : Set RuledApproximation.Plane :=
  {z | 0 ≤ z 1 ∧ z 1 ≤ (1 / 2 : ℝ) ∧ |z 0| ≤ z 1 / 2}

def edgeField (p : ℝ) (z : RuledApproximation.Plane) : RuledApproximation.Plane :=
  RuledApproximation.vec2 (edgeU p (z 0) (z 1)) (edgeV p (z 0) (z 1))

def physicalSimilarity (z : RuledApproximation.Space) : RuledApproximation.Space :=
  RuledApproximation.vec3 (z 1 / 2) (z 0 / 2) (z 2 / 2)

def labelMap (z : RuledApproximation.Plane) : RuledApproximation.Plane :=
  RuledApproximation.vec2 (z 0 / 2) (z 1)

def edgeTetrahedron : Set RuledApproximation.Space :=
  {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ |z 0| ≤ s / 2 ∧ |z 1| ≤ (1 - s) / 2 ∧
    z 2 = (1 / Real.sqrt 2) * s}

def edgeLower (p k : ℝ) (D : Set RuledApproximation.Plane) : Set RuledApproximation.Space :=
  {z | ∃ b ∈ D, ∃ y : ℝ, |y| ≤ (1 / 2 : ℝ) ∧
    z = RuledApproximation.vec3 (b 0 + k * y * edgeU p (b 0) (b 1)) y
      ((1 / Real.sqrt 2) * (b 1 + k * y * edgeV p (b 0) (b 1)))}

def edgeUpper (p k : ℝ) (D : Set RuledApproximation.Plane) : Set RuledApproximation.Space :=
  {z | ∃ b ∈ D, ∃ x : ℝ, |x| ≤ (1 / 2 : ℝ) ∧
    z = RuledApproximation.vec3 x (b 0 - k * x * edgeU p (b 0) (b 1))
      ((1 / Real.sqrt 2) * (1 - (b 1 - k * x * edgeV p (b 0) (b 1))))}

def upperSegments (p c : ℝ) (D : Set RuledApproximation.Plane) : Set RuledApproximation.Space :=
  {z | ∃ b ∈ D, ∃ y : ℝ, |y| ≤ 1 ∧
    z = RuledApproximation.vec3
      (b 0 - c * y * RuledApproximation.singularField p b 0) y
      (Real.sqrt 2 * (1 - (b 1 - c * y * RuledApproximation.singularField p b 1)))}

end SingularEdgeOne

end

end OAI
