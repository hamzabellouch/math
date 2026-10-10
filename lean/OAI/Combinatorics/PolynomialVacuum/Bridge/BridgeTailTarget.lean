import OAI.Combinatorics.HoneycombCorridor.CorridorTransfer

namespace OAI

namespace PolynomialVacuumBridge.Corridor

noncomputable def BridgeReaches {h : ℕ} (p : BridgePath h) (t : ℝ) : Prop :=
  ∃ v ∈ p.vertices, t ≤ |(position v).1|

 
def UnrestrictedBridgeTail : Prop := ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ h : ℕ, 1 ≤ h → ∀ t : ℝ, 0 ≤ t →
    bridgeTailMass h t ≤ C * Real.exp (-c*t/(h+1)) ∧
    bridgeTailLengthMass h t ≤ C*(h+1)*(h+t+1)*Real.exp (-c*t/(h+1))

end PolynomialVacuumBridge.Corridor

end OAI
