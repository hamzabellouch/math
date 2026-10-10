import OAI.Analysis.MutuallyUnbiased.PairMerge.Block11

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairTargetPermutation0 : List.Perm target0 pairMerged253 := by decide +kernel

theorem mergeConsequence0 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval target0 x = 0 := by
  rw [Integer.Sparse.eval_perm pairTargetPermutation0]
  exact pairMergedZero253 x h

theorem pairTargetPermutation1 : List.Perm target1 pairMerged360 := by decide +kernel

theorem mergeConsequence1 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval target1 x = 0 := by
  rw [Integer.Sparse.eval_perm pairTargetPermutation1]
  exact pairMergedZero360 x h

end MUB6.Certificate.PairData

end OAI
