import OAI.Probability.MatroidProphet.Main
import Mathlib.Data.Fintype.Prod

namespace OAI

/-! Concrete one-label conditional kernel for the secretary reconstruction.
The boolean records membership in the sacrificed observation mask, not branch choice.
The three coordinates are the original H, D, C coins; the T coin is not sacrificed.
-/

namespace MatroidProphet.Secretary

abbrev MaskTriple := Bool × Bool × Bool

/-- Whether at least one of the three observation coins is set. -/
def tripleRevealed (x : MaskTriple) : Bool := x.1 || x.2.1 || x.2.2

/-- The independent H,D,C law at one label, retaining the thinning parameter. -/
noncomputable def tripleWeight (t : ℝ) (x : MaskTriple) : ℝ :=
  (1 / 2) * (if x.2.1 then 1 / 4 else 3 / 4) *
    (if x.2.2 then t else 1 - t)

/-- Probability that a label is sacrificed in the main branch. -/
noncomputable def mainRevealRate : ℝ := 5 / 8 + 3 * thinningRate / 8

/-- The source specifies all seven nonzero triple masses divided by the reveal rate.
Outside the observation set the triple is deterministically zero. -/
noncomputable def conditionalTripleWeight (revealed : Bool) (x : MaskTriple) : ℝ :=
  if revealed then
    if tripleRevealed x then tripleWeight thinningRate x / mainRevealRate else 0
  else if x = (false, false, false) then 1 else 0

/-- Probability of a prescribed observation-mask membership bit. -/
noncomputable def revealBitWeight (revealed : Bool) : ℝ :=
  if revealed then mainRevealRate else 1 - mainRevealRate

end MatroidProphet.Secretary

end OAI
