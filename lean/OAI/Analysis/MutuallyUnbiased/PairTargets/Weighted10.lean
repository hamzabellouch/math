import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition10
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm10 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term10 =
      Integer.Sparse.eval integerTerm10 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition10 hH]
  norm_num [term10, integerTerm10, monomialValue10, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
