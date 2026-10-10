import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition1
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm1 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term1 =
      Integer.Sparse.eval integerTerm1 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition1 hH]
  norm_num [term1, integerTerm1, monomialValue1, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
