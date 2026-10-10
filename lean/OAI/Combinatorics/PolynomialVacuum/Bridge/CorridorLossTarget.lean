import OAI.Combinatorics.HoneycombCorridor.Bridges

namespace OAI

namespace PolynomialVacuumBridge.Corridor

 

def CorridorLossSuperpolynomial : Prop := ∀ A : ℝ, ∀ᶠ h : ℕ in Filter.atTop,
  0 ≤ bridgeMass h - confinedMass h ∧
  bridgeMass h - confinedMass h ≤ (h : ℝ)^(-A) ∧
  0 ≤ bridgeLengthMass h - confinedLengthMass h ∧
  bridgeLengthMass h - confinedLengthMass h ≤ (h : ℝ)^(-A)

end PolynomialVacuumBridge.Corridor

end OAI
