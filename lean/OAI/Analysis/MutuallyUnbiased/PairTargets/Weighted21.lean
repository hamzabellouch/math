import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition21
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm21 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term21 =
      Integer.Sparse.eval integerTerm21 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition21 hH]
  norm_num [term21, integerTerm21, monomialValue21, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
