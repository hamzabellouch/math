import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition24
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm24 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term24 =
      Integer.Sparse.eval integerTerm24 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition24 hH]
  norm_num [term24, integerTerm24, monomialValue24, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
