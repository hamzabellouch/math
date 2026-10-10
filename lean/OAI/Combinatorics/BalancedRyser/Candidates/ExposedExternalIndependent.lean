import OAI.Combinatorics.BalancedRyser.Candidates.ExposedExternalSum

namespace OAI

namespace Balanced.ExposedExternalSum
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

example (g : Direction F) (a : MergedPairs F) : oldOldSum g ∅ a = 0 := by
  simp [oldOldSum]

example (g : Direction F) (a : MergedPairs F) : oldFreshSum g ∅ a = 0 := by
  simp [oldFreshSum]

end Balanced.ExposedExternalSum

end OAI
