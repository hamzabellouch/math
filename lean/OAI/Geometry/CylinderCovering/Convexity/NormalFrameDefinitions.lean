import Mathlib

namespace OAI

noncomputable section
open scoped InnerProductSpace
namespace CylinderNormalFrame

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev BarycentricSpace := EuclideanSpace ℝ (Fin 4)

def normal (i : Fin 4) : Space :=
  (1 / Real.sqrt 3) • ![(!₂[0, Real.sqrt 2, -1] : Space),
    !₂[0, -Real.sqrt 2, -1],
    !₂[Real.sqrt 2, 0, 1],
    !₂[-Real.sqrt 2, 0, 1]] i

def frameCost (u : Space) : ℝ :=
  Real.sqrt 3 / 2 * ∑ i : Fin 4, |inner ℝ u (normal i)|

def barycentricCost (u : BarycentricSpace) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin 4, |u i|

def edgeDirection : Space := !₂[1, 0, 0]

def barycentricEdge : BarycentricSpace :=
  !₂[1 / Real.sqrt 2, -(1 / Real.sqrt 2), 0, 0]

end CylinderNormalFrame

end

end OAI
