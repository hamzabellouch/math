import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition18
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm18 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term18 =
      Integer.Sparse.eval integerTerm18 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition18 hH]
  norm_num [term18, integerTerm18, monomialValue18, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
