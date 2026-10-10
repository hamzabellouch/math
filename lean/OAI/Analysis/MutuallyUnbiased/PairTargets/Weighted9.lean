import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition9
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm9 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term9 =
      Integer.Sparse.eval integerTerm9 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition9 hH]
  norm_num [term9, integerTerm9, monomialValue9, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
