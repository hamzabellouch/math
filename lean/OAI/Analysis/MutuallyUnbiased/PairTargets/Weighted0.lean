import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition0
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm0 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term0 =
      Integer.Sparse.eval integerTerm0 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition0 hH]
  norm_num [term0, integerTerm0, monomialValue0, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
