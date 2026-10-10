import OAI.Geometry.CylinderCovering.Radial.CoordinatesDefinitions
import OAI.Geometry.CylinderCovering.Angular.CapsDefinitions

namespace OAI

noncomputable section
namespace RadialCoordinates

def firstSweep (k : ℝ) : Set BarycentricSpace :=
  {v | (∑ i, v i = 1) ∧ ∃ t S : ℝ,
    t ∈ Set.Icc 0 1 ∧ 0 ≤ S ∧ S ≤ cap k t ∧ |v 2 - v 3| ≤ 1 ∧
      v 0 = S * t + k * (v 2 - v 3) * t ^ 2 ∧
      v 1 = S * (1 - t) - k * (v 2 - v 3) * (1 - t) ^ 2}

def secondSweep (k : ℝ) : Set BarycentricSpace :=
  {v | (∑ i, v i = 1) ∧ ∃ r T : ℝ,
    r ∈ Set.Icc 0 1 ∧ 0 ≤ T ∧ T ≤ cap k r ∧ |v 0 - v 1| ≤ 1 ∧
      v 2 = T * r - k * (v 0 - v 1) * r ^ 2 ∧
      v 3 = T * (1 - r) + k * (v 0 - v 1) * (1 - r) ^ 2}

def firstSweepPoint (k t S p : ℝ) : BarycentricSpace :=
  barycentricPoint (S + k * p * angular t)
    (S * angular t + k * p * (1 + angular t ^ 2) / 2) p

def secondSweepPoint (k r T q : ℝ) : BarycentricSpace :=
  barycentricPoint (1 - T + k * q * angular r) q
    (T * angular r - k * q * (1 + angular r ^ 2) / 2)

def firstSweepWithCap (k : ℝ) (R : ℝ → ℝ) : Set BarycentricSpace :=
  (fun z : (ℝ × ℝ) × ℝ => firstSweepPoint k z.1.1 z.1.2 z.2) ''
    (AngularCaps.radialParameterSet 0 1 R ×ˢ Set.Icc (-1) 1)

def secondSweepWithCap (k : ℝ) (R : ℝ → ℝ) : Set BarycentricSpace :=
  (fun z : (ℝ × ℝ) × ℝ => secondSweepPoint k z.1.1 z.1.2 z.2) ''
    (AngularCaps.radialParameterSet 0 1 R ×ˢ Set.Icc (-1) 1)

end RadialCoordinates

end

end OAI
