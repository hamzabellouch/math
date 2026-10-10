import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition3
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm3 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term3 =
      Integer.Sparse.eval integerTerm3 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition3 hH]
  norm_num [term3, integerTerm3, monomialValue3, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
