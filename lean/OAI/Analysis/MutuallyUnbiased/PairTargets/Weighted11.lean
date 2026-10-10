import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition11
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm11 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term11 =
      Integer.Sparse.eval integerTerm11 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition11 hH]
  norm_num [term11, integerTerm11, monomialValue11, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
