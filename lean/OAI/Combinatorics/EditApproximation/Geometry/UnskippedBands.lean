import OAI.Combinatorics.EditApproximation.Geometry.BandActionGuards
import OAI.Combinatorics.EditApproximation.Geometry.StateDomain
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Literal unskipped-band tests

The finite representative band, rational child envelopes and canonical
rounded action are tested directly. A successful result carries exactly
the facts checked by the algorithm; inaccurate seeds still produce a
finite list of such tested records.
-/

namespace EditApproximation

open Finset







namespace UnskippedBand







theorem envelope_pos {α : Type*} {source target : List α} {M : ℕ}
    {parent : TargetInterval source.length} {b P thetaExponent : ℕ}
    {tau F : ℚ} {child initial : Fin M → TargetInterval target.length → ℚ}
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial) (i : Fin M) :
    0 < member.envelope i :=
  bandChildEnvelope_pos b member.actions initial i

end UnskippedBand

end EditApproximation

end OAI
