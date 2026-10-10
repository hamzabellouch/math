import Mathlib

namespace OAI

namespace CylinderCovering.SimplexDiameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ChordLength (S : Set E) (u : E) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∃ x ∈ S, x + r • u ∈ S

noncomputable def maxChord (S : Set E) (u : E) : ℝ :=
  sSup {r : ℝ | ChordLength S u r}

end CylinderCovering.SimplexDiameter

end OAI
