import OAI.Geometry.CylinderCovering.Angular.ConstructionDefinitions

namespace OAI

open Set
noncomputable section
namespace TriangularCovering

def lowerIntercept (a b T : ℝ) : Set Space :=
  {z | ∃ y t : ℝ, 0 ≤ t ∧ t ≤ T ∧ a * t ≤ y ∧ y ≤ b * t ∧ z = point 0 y t}

def upperIntercept (a b T : ℝ) : Set Space :=
  {z | ∃ x s : ℝ, 0 ≤ s ∧ s ≤ T ∧ a * s ≤ x ∧ x ≤ b * s ∧ z = point x 0 (1-s)}

end TriangularCovering

end

end OAI
