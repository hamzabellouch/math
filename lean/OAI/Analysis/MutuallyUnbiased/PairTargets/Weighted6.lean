import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition6
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm6 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term6 =
      Integer.Sparse.eval integerTerm6 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition6 hH]
  norm_num [term6, integerTerm6, monomialValue6, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
