import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition25
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm25 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term25 =
      Integer.Sparse.eval integerTerm25 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition25 hH]
  norm_num [term25, integerTerm25, monomialValue25, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
