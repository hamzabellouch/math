import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition13
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm13 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term13 =
      Integer.Sparse.eval integerTerm13 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition13 hH]
  norm_num [term13, integerTerm13, monomialValue13, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
