import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition14
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm14 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term14 =
      Integer.Sparse.eval integerTerm14 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition14 hH]
  norm_num [term14, integerTerm14, monomialValue14, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
