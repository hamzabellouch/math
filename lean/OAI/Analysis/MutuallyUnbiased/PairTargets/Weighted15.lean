import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition15
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm15 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term15 =
      Integer.Sparse.eval integerTerm15 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition15 hH]
  norm_num [term15, integerTerm15, monomialValue15, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
