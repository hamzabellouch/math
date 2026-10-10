import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition20
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm20 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term20 =
      Integer.Sparse.eval integerTerm20 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition20 hH]
  norm_num [term20, integerTerm20, monomialValue20, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
