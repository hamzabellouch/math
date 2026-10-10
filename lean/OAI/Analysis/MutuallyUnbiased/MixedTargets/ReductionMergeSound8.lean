import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData8
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound7
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound8
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound9

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval256 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge256 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge256 (originalVector B) := by
  rw [reducedMerge256Check, Integer.Sparse.eval_mergeBy, reducedMergeEval254 B hB hF, reducedMergeEval255 B hB hF]
  rw [originalMerge256, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval257 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge257 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge257 (originalVector B) := by
  rw [reducedMerge257Check, Integer.Sparse.eval_mergeBy, reducedMergeEval253 B hB hF, reducedMergeEval256 B hB hF]
  rw [originalMerge257, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval258 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge258 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge258 (originalVector B) := by
  rw [reducedMerge258Check, Integer.Sparse.eval_mergeBy, reducedTermEval261 B hB hF, reducedTermEval262 B hB hF]
  rw [originalMerge258, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval259 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge259 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge259 (originalVector B) := by
  rw [reducedMerge259Check, Integer.Sparse.eval_mergeBy, reducedTermEval263 B hB hF, reducedTermEval264 B hB hF]
  rw [originalMerge259, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval260 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge260 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge260 (originalVector B) := by
  rw [reducedMerge260Check, Integer.Sparse.eval_mergeBy, reducedMergeEval258 B hB hF, reducedMergeEval259 B hB hF]
  rw [originalMerge260, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval261 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge261 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge261 (originalVector B) := by
  rw [reducedMerge261Check, Integer.Sparse.eval_mergeBy, reducedTermEval265 B hB hF, reducedTermEval266 B hB hF]
  rw [originalMerge261, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval262 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge262 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge262 (originalVector B) := by
  rw [reducedMerge262Check, Integer.Sparse.eval_mergeBy, reducedTermEval267 B hB hF, reducedTermEval268 B hB hF]
  rw [originalMerge262, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge263 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge263 (originalVector B) := by
  rw [reducedMerge263Check, Integer.Sparse.eval_mergeBy, reducedMergeEval261 B hB hF, reducedMergeEval262 B hB hF]
  rw [originalMerge263, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge264 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge264 (originalVector B) := by
  rw [reducedMerge264Check, Integer.Sparse.eval_mergeBy, reducedMergeEval260 B hB hF, reducedMergeEval263 B hB hF]
  rw [originalMerge264, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge265 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge265 (originalVector B) := by
  rw [reducedMerge265Check, Integer.Sparse.eval_mergeBy, reducedMergeEval257 B hB hF, reducedMergeEval264 B hB hF]
  rw [originalMerge265, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval266 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge266 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge266 (originalVector B) := by
  rw [reducedMerge266Check, Integer.Sparse.eval_mergeBy, reducedMergeEval251 B hB hF, reducedMergeEval265 B hB hF]
  rw [originalMerge266, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval267 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge267 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge267 (originalVector B) := by
  rw [reducedMerge267Check, Integer.Sparse.eval_mergeBy, reducedTermEval270 B hB hF, reducedTermEval271 B hB hF]
  rw [originalMerge267, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge268 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge268 (originalVector B) := by
  rw [reducedMerge268Check, Integer.Sparse.eval_mergeBy, reducedTermEval269 B hB hF, reducedMergeEval267 B hB hF]
  rw [originalMerge268, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval269 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge269 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge269 (originalVector B) := by
  rw [reducedMerge269Check, Integer.Sparse.eval_mergeBy, reducedTermEval272 B hB hF, reducedTermEval273 B hB hF]
  rw [originalMerge269, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval270 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge270 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge270 (originalVector B) := by
  rw [reducedMerge270Check, Integer.Sparse.eval_mergeBy, reducedTermEval274 B hB hF, reducedTermEval275 B hB hF]
  rw [originalMerge270, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval271 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge271 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge271 (originalVector B) := by
  rw [reducedMerge271Check, Integer.Sparse.eval_mergeBy, reducedMergeEval269 B hB hF, reducedMergeEval270 B hB hF]
  rw [originalMerge271, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval272 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge272 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge272 (originalVector B) := by
  rw [reducedMerge272Check, Integer.Sparse.eval_mergeBy, reducedMergeEval268 B hB hF, reducedMergeEval271 B hB hF]
  rw [originalMerge272, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge273 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge273 (originalVector B) := by
  rw [reducedMerge273Check, Integer.Sparse.eval_mergeBy, reducedTermEval276 B hB hF, reducedTermEval277 B hB hF]
  rw [originalMerge273, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge274 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge274 (originalVector B) := by
  rw [reducedMerge274Check, Integer.Sparse.eval_mergeBy, reducedTermEval278 B hB hF, reducedTermEval279 B hB hF]
  rw [originalMerge274, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval275 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge275 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge275 (originalVector B) := by
  rw [reducedMerge275Check, Integer.Sparse.eval_mergeBy, reducedMergeEval273 B hB hF, reducedMergeEval274 B hB hF]
  rw [originalMerge275, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval276 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge276 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge276 (originalVector B) := by
  rw [reducedMerge276Check, Integer.Sparse.eval_mergeBy, reducedTermEval280 B hB hF, reducedTermEval281 B hB hF]
  rw [originalMerge276, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval277 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge277 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge277 (originalVector B) := by
  rw [reducedMerge277Check, Integer.Sparse.eval_mergeBy, reducedTermEval282 B hB hF, reducedTermEval283 B hB hF]
  rw [originalMerge277, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval278 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge278 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge278 (originalVector B) := by
  rw [reducedMerge278Check, Integer.Sparse.eval_mergeBy, reducedMergeEval276 B hB hF, reducedMergeEval277 B hB hF]
  rw [originalMerge278, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval279 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge279 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge279 (originalVector B) := by
  rw [reducedMerge279Check, Integer.Sparse.eval_mergeBy, reducedMergeEval275 B hB hF, reducedMergeEval278 B hB hF]
  rw [originalMerge279, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge280 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge280 (originalVector B) := by
  rw [reducedMerge280Check, Integer.Sparse.eval_mergeBy, reducedMergeEval272 B hB hF, reducedMergeEval279 B hB hF]
  rw [originalMerge280, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval281 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge281 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge281 (originalVector B) := by
  rw [reducedMerge281Check, Integer.Sparse.eval_mergeBy, reducedTermEval285 B hB hF, reducedTermEval286 B hB hF]
  rw [originalMerge281, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval282 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge282 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge282 (originalVector B) := by
  rw [reducedMerge282Check, Integer.Sparse.eval_mergeBy, reducedTermEval284 B hB hF, reducedMergeEval281 B hB hF]
  rw [originalMerge282, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge283 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge283 (originalVector B) := by
  rw [reducedMerge283Check, Integer.Sparse.eval_mergeBy, reducedTermEval287 B hB hF, reducedTermEval288 B hB hF]
  rw [originalMerge283, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge284 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge284 (originalVector B) := by
  rw [reducedMerge284Check, Integer.Sparse.eval_mergeBy, reducedTermEval289 B hB hF, reducedTermEval290 B hB hF]
  rw [originalMerge284, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge285 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge285 (originalVector B) := by
  rw [reducedMerge285Check, Integer.Sparse.eval_mergeBy, reducedMergeEval283 B hB hF, reducedMergeEval284 B hB hF]
  rw [originalMerge285, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval286 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge286 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge286 (originalVector B) := by
  rw [reducedMerge286Check, Integer.Sparse.eval_mergeBy, reducedMergeEval282 B hB hF, reducedMergeEval285 B hB hF]
  rw [originalMerge286, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval287 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge287 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge287 (originalVector B) := by
  rw [reducedMerge287Check, Integer.Sparse.eval_mergeBy, reducedTermEval291 B hB hF, reducedTermEval292 B hB hF]
  rw [originalMerge287, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
