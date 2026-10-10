import Mathlib

namespace OAI

noncomputable section
namespace AngularGeometry

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)

def lowerCarrier (h τ α β : ℝ) (P : Set Plane) : Set Space :=
  {z | ∃ p ∈ P, ∃ x : ℝ,
    z = WithLp.toLp 2 ![x, p 0 + τ * α * x, h * (p 1 + τ * β * x)]}

def upperCarrier (h τ α β : ℝ) (P : Set Plane) : Set Space :=
  {z | ∃ p ∈ P, ∃ y : ℝ,
    z = WithLp.toLp 2 ![p 0 - τ * α * y, y, h * (1 - p 1 + τ * β * y)]}

def areaFactor (h τ α β : ℝ) : ℝ :=
  h / Real.sqrt (1 + τ ^ 2 * (α ^ 2 + h ^ 2 * β ^ 2))

end AngularGeometry

end

end OAI
