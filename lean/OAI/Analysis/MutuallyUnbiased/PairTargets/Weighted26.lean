import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition26
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm26 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term26 =
      Integer.Sparse.eval integerTerm26 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition26 hH]
  norm_num [term26, integerTerm26, monomialValue26, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
