import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition5
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm5 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term5 =
      Integer.Sparse.eval integerTerm5 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition5 hH]
  norm_num [term5, integerTerm5, monomialValue5, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
