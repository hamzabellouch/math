import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition12
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm12 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term12 =
      Integer.Sparse.eval integerTerm12 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition12 hH]
  norm_num [term12, integerTerm12, monomialValue12, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
