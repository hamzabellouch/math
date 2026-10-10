import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition7
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm7 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term7 =
      Integer.Sparse.eval integerTerm7 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition7 hH]
  norm_num [term7, integerTerm7, monomialValue7, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
