import OAI.Geometry.CylinderCovering.Rational.FieldDefinitions

namespace OAI

open MeasureTheory

noncomputable section

namespace SlopeRational

def baseDomain : Set Plane := wedge ∩ {z | 0 ≤ z 1}

def energyDensity (d : ℝ) (z : Plane) : ℝ :=
  (a d (z 0) (z 1))^2 + (1/2)*(b d (z 0) (z 1))^2

def energyIntegral (d : ℝ) : ℝ := (1/2) * ∫ z in baseDomain, energyDensity d z

end SlopeRational

end

end OAI
