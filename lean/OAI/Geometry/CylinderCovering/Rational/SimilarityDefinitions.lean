import Mathlib

namespace OAI

noncomputable section
namespace RationalSimilarity
abbrev Space := EuclideanSpace ℝ (Fin 3)

def h : ℝ := 1 / Real.sqrt 2

def ell : ℝ := 1 / (2 * Real.sqrt 2)

def reflection (z : Space) : Space := !₂[-z 0, z 1, -z 2]

def phi (z : Space) : Space := !₂[-ell * z 0, ell * z 1, ell * (1 - z 2)]

def uncenteredTetrahedron : Set Space :=
  {z | 0 ≤ z 2 ∧ z 2 ≤ 2 ∧ |z 1| ≤ h * z 2 ∧ |z 0| ≤ h * (2 - z 2)}

def centeredTetrahedron : Set Space :=
  {z | ∃ t : ℝ, z 2 = h * t ∧ -(1 / 2 : ℝ) ≤ t ∧ t ≤ 1 / 2 ∧
    |z 0| ≤ (1 / 2 + t) / 2 ∧ |z 1| ≤ (1 / 2 - t) / 2}
end RationalSimilarity

end

end OAI
