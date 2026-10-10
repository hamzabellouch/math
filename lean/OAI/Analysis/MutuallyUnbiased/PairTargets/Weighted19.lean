import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition19
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm19 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term19 =
      Integer.Sparse.eval integerTerm19 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition19 hH]
  norm_num [term19, integerTerm19, monomialValue19, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
