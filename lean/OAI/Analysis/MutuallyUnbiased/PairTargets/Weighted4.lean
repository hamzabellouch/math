import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition4
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm4 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term4 =
      Integer.Sparse.eval integerTerm4 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition4 hH]
  norm_num [term4, integerTerm4, monomialValue4, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
