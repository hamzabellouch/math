import OAI.Geometry.CylinderCovering.Cartesian.CapsDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.CartesianCaps

def height (τ η y : ℝ) : ℝ := 1/2 + τ^2 * (D y + η)

def domain (τ η b : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ b ∧ |p.1| ≤ p.2 ∧ p.2 ≤ height τ η p.1}

def central (τ η : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (-1/2 : ℝ) (1/2) ∧ p.2 ∈ Set.Icc |p.1| (height τ η p.1)}

end CylinderCovering.CartesianCaps

end

end OAI
