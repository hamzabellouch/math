import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition2
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm2 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term2 =
      Integer.Sparse.eval integerTerm2 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition2 hH]
  norm_num [term2, integerTerm2, monomialValue2, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
