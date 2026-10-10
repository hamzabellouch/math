import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition17
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm17 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term17 =
      Integer.Sparse.eval integerTerm17 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition17 hH]
  norm_num [term17, integerTerm17, monomialValue17, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
