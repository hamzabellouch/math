import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Concrete sacrificed-mask data for the secretary transport.

The branch and every mask coordinate are functions of the complete source seed.
The test mask is deliberately not part of the sacrificed mask.
-/

namespace MatroidProphet.Secretary

/-- The observation mask of the concrete source rule, before any values are seen. -/
noncomputable def sourceMask {n : ℕ} (r : Seed (mainSeedBits n)) : Finset (Fin n) :=
  if mainBranch r then
    (mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C
  else (mainMasks r).H

/-- Literal branchwise Bernoulli rates from `sections/secretary.tex`.
`false` is the maximum branch and `true` is the main branch. -/
noncomputable def branchRate (j : Bool) : ℝ :=
  if j then 5 / 8 + 3 * ((2 : ℝ) ^ 143)⁻¹ else 1 / 2

end MatroidProphet.Secretary

end OAI
