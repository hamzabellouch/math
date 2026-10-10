import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData11
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound10
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound9
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound11
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound12

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval352 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge352 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge352 (originalVector B) := by
  rw [reducedMerge352Check, Integer.Sparse.eval_mergeBy, reducedMergeEval348 B hB hF, reducedMergeEval351 B hB hF]
  rw [originalMerge352, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval353 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge353 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge353 (originalVector B) := by
  rw [reducedMerge353Check, Integer.Sparse.eval_mergeBy, reducedMergeEval345 B hB hF, reducedMergeEval352 B hB hF]
  rw [originalMerge353, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval354 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge354 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge354 (originalVector B) := by
  rw [reducedMerge354Check, Integer.Sparse.eval_mergeBy, reducedMergeEval339 B hB hF, reducedMergeEval353 B hB hF]
  rw [originalMerge354, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval355 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge355 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge355 (originalVector B) := by
  rw [reducedMerge355Check, Integer.Sparse.eval_mergeBy, reducedMergeEval325 B hB hF, reducedMergeEval354 B hB hF]
  rw [originalMerge355, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval356 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge356 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge356 (originalVector B) := by
  rw [reducedMerge356Check, Integer.Sparse.eval_mergeBy, reducedMergeEval296 B hB hF, reducedMergeEval355 B hB hF]
  rw [originalMerge356, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval357 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge357 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge357 (originalVector B) := by
  rw [reducedMerge357Check, Integer.Sparse.eval_mergeBy, reducedTermEval360 B hB hF, reducedTermEval361 B hB hF]
  rw [originalMerge357, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval358 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge358 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge358 (originalVector B) := by
  rw [reducedMerge358Check, Integer.Sparse.eval_mergeBy, reducedTermEval359 B hB hF, reducedMergeEval357 B hB hF]
  rw [originalMerge358, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval359 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge359 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge359 (originalVector B) := by
  rw [reducedMerge359Check, Integer.Sparse.eval_mergeBy, reducedTermEval362 B hB hF, reducedTermEval363 B hB hF]
  rw [originalMerge359, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval360 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge360 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge360 (originalVector B) := by
  rw [reducedMerge360Check, Integer.Sparse.eval_mergeBy, reducedTermEval364 B hB hF, reducedTermEval365 B hB hF]
  rw [originalMerge360, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval361 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge361 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge361 (originalVector B) := by
  rw [reducedMerge361Check, Integer.Sparse.eval_mergeBy, reducedMergeEval359 B hB hF, reducedMergeEval360 B hB hF]
  rw [originalMerge361, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval362 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge362 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge362 (originalVector B) := by
  rw [reducedMerge362Check, Integer.Sparse.eval_mergeBy, reducedMergeEval358 B hB hF, reducedMergeEval361 B hB hF]
  rw [originalMerge362, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval363 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge363 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge363 (originalVector B) := by
  rw [reducedMerge363Check, Integer.Sparse.eval_mergeBy, reducedTermEval366 B hB hF, reducedTermEval367 B hB hF]
  rw [originalMerge363, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval364 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge364 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge364 (originalVector B) := by
  rw [reducedMerge364Check, Integer.Sparse.eval_mergeBy, reducedTermEval368 B hB hF, reducedTermEval369 B hB hF]
  rw [originalMerge364, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval365 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge365 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge365 (originalVector B) := by
  rw [reducedMerge365Check, Integer.Sparse.eval_mergeBy, reducedMergeEval363 B hB hF, reducedMergeEval364 B hB hF]
  rw [originalMerge365, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval366 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge366 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge366 (originalVector B) := by
  rw [reducedMerge366Check, Integer.Sparse.eval_mergeBy, reducedTermEval370 B hB hF, reducedTermEval371 B hB hF]
  rw [originalMerge366, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge367 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge367 (originalVector B) := by
  rw [reducedMerge367Check, Integer.Sparse.eval_mergeBy, reducedTermEval372 B hB hF, reducedTermEval373 B hB hF]
  rw [originalMerge367, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval368 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge368 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge368 (originalVector B) := by
  rw [reducedMerge368Check, Integer.Sparse.eval_mergeBy, reducedMergeEval366 B hB hF, reducedMergeEval367 B hB hF]
  rw [originalMerge368, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge369 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge369 (originalVector B) := by
  rw [reducedMerge369Check, Integer.Sparse.eval_mergeBy, reducedMergeEval365 B hB hF, reducedMergeEval368 B hB hF]
  rw [originalMerge369, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval370 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge370 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge370 (originalVector B) := by
  rw [reducedMerge370Check, Integer.Sparse.eval_mergeBy, reducedMergeEval362 B hB hF, reducedMergeEval369 B hB hF]
  rw [originalMerge370, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge371 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge371 (originalVector B) := by
  rw [reducedMerge371Check, Integer.Sparse.eval_mergeBy, reducedTermEval375 B hB hF, reducedTermEval376 B hB hF]
  rw [originalMerge371, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge372 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge372 (originalVector B) := by
  rw [reducedMerge372Check, Integer.Sparse.eval_mergeBy, reducedTermEval374 B hB hF, reducedMergeEval371 B hB hF]
  rw [originalMerge372, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval373 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge373 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge373 (originalVector B) := by
  rw [reducedMerge373Check, Integer.Sparse.eval_mergeBy, reducedTermEval377 B hB hF, reducedTermEval378 B hB hF]
  rw [originalMerge373, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval374 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge374 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge374 (originalVector B) := by
  rw [reducedMerge374Check, Integer.Sparse.eval_mergeBy, reducedTermEval379 B hB hF, reducedTermEval380 B hB hF]
  rw [originalMerge374, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval375 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge375 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge375 (originalVector B) := by
  rw [reducedMerge375Check, Integer.Sparse.eval_mergeBy, reducedMergeEval373 B hB hF, reducedMergeEval374 B hB hF]
  rw [originalMerge375, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval376 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge376 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge376 (originalVector B) := by
  rw [reducedMerge376Check, Integer.Sparse.eval_mergeBy, reducedMergeEval372 B hB hF, reducedMergeEval375 B hB hF]
  rw [originalMerge376, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval377 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge377 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge377 (originalVector B) := by
  rw [reducedMerge377Check, Integer.Sparse.eval_mergeBy, reducedTermEval381 B hB hF, reducedTermEval382 B hB hF]
  rw [originalMerge377, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval378 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge378 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge378 (originalVector B) := by
  rw [reducedMerge378Check, Integer.Sparse.eval_mergeBy, reducedTermEval383 B hB hF, reducedTermEval384 B hB hF]
  rw [originalMerge378, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval379 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge379 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge379 (originalVector B) := by
  rw [reducedMerge379Check, Integer.Sparse.eval_mergeBy, reducedMergeEval377 B hB hF, reducedMergeEval378 B hB hF]
  rw [originalMerge379, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval380 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge380 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge380 (originalVector B) := by
  rw [reducedMerge380Check, Integer.Sparse.eval_mergeBy, reducedTermEval385 B hB hF, reducedTermEval386 B hB hF]
  rw [originalMerge380, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval381 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge381 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge381 (originalVector B) := by
  rw [reducedMerge381Check, Integer.Sparse.eval_mergeBy, reducedTermEval387 B hB hF, reducedTermEval388 B hB hF]
  rw [originalMerge381, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval382 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge382 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge382 (originalVector B) := by
  rw [reducedMerge382Check, Integer.Sparse.eval_mergeBy, reducedMergeEval380 B hB hF, reducedMergeEval381 B hB hF]
  rw [originalMerge382, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval383 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge383 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge383 (originalVector B) := by
  rw [reducedMerge383Check, Integer.Sparse.eval_mergeBy, reducedMergeEval379 B hB hF, reducedMergeEval382 B hB hF]
  rw [originalMerge383, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

end MUB6.Certificate.MixedTargetSemantics

end OAI
