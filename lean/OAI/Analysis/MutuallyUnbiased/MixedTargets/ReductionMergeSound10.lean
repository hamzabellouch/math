import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData10
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound9
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound10
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound11

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge320 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge320 (originalVector B) := by
  rw [reducedMerge320Check, Integer.Sparse.eval_mergeBy, reducedTermEval325 B hB hF, reducedTermEval326 B hB hF]
  rw [originalMerge320, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval321 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge321 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge321 (originalVector B) := by
  rw [reducedMerge321Check, Integer.Sparse.eval_mergeBy, reducedTermEval327 B hB hF, reducedTermEval328 B hB hF]
  rw [originalMerge321, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge322 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge322 (originalVector B) := by
  rw [reducedMerge322Check, Integer.Sparse.eval_mergeBy, reducedMergeEval320 B hB hF, reducedMergeEval321 B hB hF]
  rw [originalMerge322, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge323 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge323 (originalVector B) := by
  rw [reducedMerge323Check, Integer.Sparse.eval_mergeBy, reducedMergeEval319 B hB hF, reducedMergeEval322 B hB hF]
  rw [originalMerge323, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval324 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge324 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge324 (originalVector B) := by
  rw [reducedMerge324Check, Integer.Sparse.eval_mergeBy, reducedMergeEval316 B hB hF, reducedMergeEval323 B hB hF]
  rw [originalMerge324, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge325 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge325 (originalVector B) := by
  rw [reducedMerge325Check, Integer.Sparse.eval_mergeBy, reducedMergeEval310 B hB hF, reducedMergeEval324 B hB hF]
  rw [originalMerge325, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval326 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge326 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge326 (originalVector B) := by
  rw [reducedMerge326Check, Integer.Sparse.eval_mergeBy, reducedTermEval330 B hB hF, reducedTermEval331 B hB hF]
  rw [originalMerge326, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge327 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge327 (originalVector B) := by
  rw [reducedMerge327Check, Integer.Sparse.eval_mergeBy, reducedTermEval329 B hB hF, reducedMergeEval326 B hB hF]
  rw [originalMerge327, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge328 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge328 (originalVector B) := by
  rw [reducedMerge328Check, Integer.Sparse.eval_mergeBy, reducedTermEval332 B hB hF, reducedTermEval333 B hB hF]
  rw [originalMerge328, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge329 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge329 (originalVector B) := by
  rw [reducedMerge329Check, Integer.Sparse.eval_mergeBy, reducedTermEval334 B hB hF, reducedTermEval335 B hB hF]
  rw [originalMerge329, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge330 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge330 (originalVector B) := by
  rw [reducedMerge330Check, Integer.Sparse.eval_mergeBy, reducedMergeEval328 B hB hF, reducedMergeEval329 B hB hF]
  rw [originalMerge330, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge331 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge331 (originalVector B) := by
  rw [reducedMerge331Check, Integer.Sparse.eval_mergeBy, reducedMergeEval327 B hB hF, reducedMergeEval330 B hB hF]
  rw [originalMerge331, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge332 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge332 (originalVector B) := by
  rw [reducedMerge332Check, Integer.Sparse.eval_mergeBy, reducedTermEval336 B hB hF, reducedTermEval337 B hB hF]
  rw [originalMerge332, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge333 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge333 (originalVector B) := by
  rw [reducedMerge333Check, Integer.Sparse.eval_mergeBy, reducedTermEval338 B hB hF, reducedTermEval339 B hB hF]
  rw [originalMerge333, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge334 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge334 (originalVector B) := by
  rw [reducedMerge334Check, Integer.Sparse.eval_mergeBy, reducedMergeEval332 B hB hF, reducedMergeEval333 B hB hF]
  rw [originalMerge334, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval335 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge335 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge335 (originalVector B) := by
  rw [reducedMerge335Check, Integer.Sparse.eval_mergeBy, reducedTermEval340 B hB hF, reducedTermEval341 B hB hF]
  rw [originalMerge335, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge336 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge336 (originalVector B) := by
  rw [reducedMerge336Check, Integer.Sparse.eval_mergeBy, reducedTermEval342 B hB hF, reducedTermEval343 B hB hF]
  rw [originalMerge336, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge337 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge337 (originalVector B) := by
  rw [reducedMerge337Check, Integer.Sparse.eval_mergeBy, reducedMergeEval335 B hB hF, reducedMergeEval336 B hB hF]
  rw [originalMerge337, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge338 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge338 (originalVector B) := by
  rw [reducedMerge338Check, Integer.Sparse.eval_mergeBy, reducedMergeEval334 B hB hF, reducedMergeEval337 B hB hF]
  rw [originalMerge338, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval339 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge339 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge339 (originalVector B) := by
  rw [reducedMerge339Check, Integer.Sparse.eval_mergeBy, reducedMergeEval331 B hB hF, reducedMergeEval338 B hB hF]
  rw [originalMerge339, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval340 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge340 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge340 (originalVector B) := by
  rw [reducedMerge340Check, Integer.Sparse.eval_mergeBy, reducedTermEval345 B hB hF, reducedTermEval346 B hB hF]
  rw [originalMerge340, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval341 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge341 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge341 (originalVector B) := by
  rw [reducedMerge341Check, Integer.Sparse.eval_mergeBy, reducedTermEval344 B hB hF, reducedMergeEval340 B hB hF]
  rw [originalMerge341, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval342 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge342 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge342 (originalVector B) := by
  rw [reducedMerge342Check, Integer.Sparse.eval_mergeBy, reducedTermEval347 B hB hF, reducedTermEval348 B hB hF]
  rw [originalMerge342, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval343 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge343 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge343 (originalVector B) := by
  rw [reducedMerge343Check, Integer.Sparse.eval_mergeBy, reducedTermEval349 B hB hF, reducedTermEval350 B hB hF]
  rw [originalMerge343, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval344 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge344 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge344 (originalVector B) := by
  rw [reducedMerge344Check, Integer.Sparse.eval_mergeBy, reducedMergeEval342 B hB hF, reducedMergeEval343 B hB hF]
  rw [originalMerge344, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval345 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge345 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge345 (originalVector B) := by
  rw [reducedMerge345Check, Integer.Sparse.eval_mergeBy, reducedMergeEval341 B hB hF, reducedMergeEval344 B hB hF]
  rw [originalMerge345, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval346 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge346 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge346 (originalVector B) := by
  rw [reducedMerge346Check, Integer.Sparse.eval_mergeBy, reducedTermEval351 B hB hF, reducedTermEval352 B hB hF]
  rw [originalMerge346, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval347 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge347 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge347 (originalVector B) := by
  rw [reducedMerge347Check, Integer.Sparse.eval_mergeBy, reducedTermEval353 B hB hF, reducedTermEval354 B hB hF]
  rw [originalMerge347, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge348 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge348 (originalVector B) := by
  rw [reducedMerge348Check, Integer.Sparse.eval_mergeBy, reducedMergeEval346 B hB hF, reducedMergeEval347 B hB hF]
  rw [originalMerge348, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval349 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge349 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge349 (originalVector B) := by
  rw [reducedMerge349Check, Integer.Sparse.eval_mergeBy, reducedTermEval355 B hB hF, reducedTermEval356 B hB hF]
  rw [originalMerge349, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval350 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge350 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge350 (originalVector B) := by
  rw [reducedMerge350Check, Integer.Sparse.eval_mergeBy, reducedTermEval357 B hB hF, reducedTermEval358 B hB hF]
  rw [originalMerge350, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval351 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge351 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge351 (originalVector B) := by
  rw [reducedMerge351Check, Integer.Sparse.eval_mergeBy, reducedMergeEval349 B hB hF, reducedMergeEval350 B hB hF]
  rw [originalMerge351, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
