import OAI.Combinatorics.BooleanFunctions.Amplification
import OAI.Combinatorics.BooleanFunctions.Readout

namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-- Every stage and the final sign readout use finitely many actual Boolean inputs. -/
theorem signed_violations : SignedViolations := by
  intro C hC
  obtain ⟨F,hF⟩ := Amplification.exists_large_ratio ((C/ReadoutCLT.constant)^2)
  exact Observations.violation_of_observation F.map F.cost F.cost_pos F.cell_le
    F.variance_pos C hC hF

/-- Unbounded violations for ordinary real Fourier degree and uniform cube averages. -/
theorem main : SignedViolations ∧ ¬ BddAbove AbsoluteRatios := by
  exact ⟨signed_violations,absolute_unbounded_of_signed signed_violations⟩

end SquareRootDegree

end

end OAI
