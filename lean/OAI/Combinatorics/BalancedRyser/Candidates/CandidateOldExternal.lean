import OAI.Combinatorics.BalancedRyser.Candidates.CandidateOldExternalOverlap

namespace OAI

universe u
example (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (g : Balanced.Direction F) (D : Finset (Balanced.Direction F))
    (a : Balanced.MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :=
  Balanced.CandidateOldExternal.expected_oldOverlapWitnesses_le g D a m hD

end OAI
