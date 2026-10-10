import Mathlib

namespace OAI

open MeasureTheory

noncomputable section

namespace RationalCoefficients

def angularA0 (d r : ℝ) : ℝ := r * (r + 2*d) / (16*(r+d)^2)

def angularA2 (d r : ℝ) : ℝ := r^2 / (4*(r+d)^2)

def angularB1 (d r : ℝ) : ℝ := r / (2*(r+d))

def angularEnergy (d r z : ℝ) : ℝ :=
  (angularA0 d r + angularA2 d r * z^2)^2 + (1/2)*(angularB1 d r * z)^2

def radialDensity (d r : ℝ) : ℝ :=
  r * ((angularA0 d r)^2 +
    (2*angularA0 d r*angularA2 d r+(angularB1 d r)^2/2)/12 +
    (angularA2 d r)^2/80)

def polarCost (d : ℝ) : ℝ :=
  (1/2) * ∫ r in (0:ℝ)..(1/2), r * ∫ z in (-(1/2:ℝ))..(1/2), angularEnergy d r z

def wedgeCost (d : ℝ) : ℝ :=
  (1/2) * ∫ r in (0:ℝ)..(1/2), ∫ y in (-r/2)..(r/2),
    ((y^2/(4*(r+d)^2) + r*(r+2*d)/(16*(r+d)^2))^2 +
      (1/2)*(y/(2*(r+d)))^2)

end RationalCoefficients

end

end OAI
