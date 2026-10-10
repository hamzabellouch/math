import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition23
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm23 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term23 =
      Integer.Sparse.eval integerTerm23 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition23 hH]
  norm_num [term23, integerTerm23, monomialValue23, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
