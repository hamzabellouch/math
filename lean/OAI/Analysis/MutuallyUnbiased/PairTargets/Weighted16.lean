import OAI.Analysis.MutuallyUnbiased.PairTargets.Partition16
import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm16 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term16 =
      Integer.Sparse.eval integerTerm16 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition16 hH]
  norm_num [term16, integerTerm16, monomialValue16, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
