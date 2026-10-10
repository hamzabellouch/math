import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition22
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm22 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term22 =
      Integer.Sparse.eval integerTerm22 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition22 hH]
  norm_num [term22, integerTerm22, monomialValue22, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
