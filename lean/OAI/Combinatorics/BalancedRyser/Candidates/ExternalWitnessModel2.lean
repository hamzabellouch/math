import OAI.Combinatorics.BalancedRyser.Candidates.ExternalWitnessModel

namespace OAI

example (F : Type 2) [Field F] [Fintype F] [DecidableEq F]
    (g : Balanced.Direction F) (M : Balanced.MergedPairs F) :
    (Balanced.ExternalAssembly.patternModel g).count M =
      ((Balanced.ExternalAssembly.witnesses g M).card : ℝ) :=
  Balanced.ExternalAssembly.patternModel_count g M

end OAI
