import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition8
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm8 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term8 =
      Integer.Sparse.eval integerTerm8 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition8 hH]
  norm_num [term8, integerTerm8, monomialValue8, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
