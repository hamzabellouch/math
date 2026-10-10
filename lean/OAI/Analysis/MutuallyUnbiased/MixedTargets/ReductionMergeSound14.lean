import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData14
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound11
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound12
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound13
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound7
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound14
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound15

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval448 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge448 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge448 (originalVector B) := by
  rw [reducedMerge448Check, Integer.Sparse.eval_mergeBy, reducedTermEval454 B hB hF, reducedTermEval455 B hB hF]
  rw [originalMerge448, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge449 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge449 (originalVector B) := by
  rw [reducedMerge449Check, Integer.Sparse.eval_mergeBy, reducedMergeEval447 B hB hF, reducedMergeEval448 B hB hF]
  rw [originalMerge449, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge450 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge450 (originalVector B) := by
  rw [reducedMerge450Check, Integer.Sparse.eval_mergeBy, reducedMergeEval446 B hB hF, reducedMergeEval449 B hB hF]
  rw [originalMerge450, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge451 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge451 (originalVector B) := by
  rw [reducedMerge451Check, Integer.Sparse.eval_mergeBy, reducedTermEval456 B hB hF, reducedTermEval457 B hB hF]
  rw [originalMerge451, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge452 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge452 (originalVector B) := by
  rw [reducedMerge452Check, Integer.Sparse.eval_mergeBy, reducedTermEval458 B hB hF, reducedTermEval459 B hB hF]
  rw [originalMerge452, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval453 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge453 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge453 (originalVector B) := by
  rw [reducedMerge453Check, Integer.Sparse.eval_mergeBy, reducedMergeEval451 B hB hF, reducedMergeEval452 B hB hF]
  rw [originalMerge453, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge454 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge454 (originalVector B) := by
  rw [reducedMerge454Check, Integer.Sparse.eval_mergeBy, reducedTermEval460 B hB hF, reducedTermEval461 B hB hF]
  rw [originalMerge454, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge455 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge455 (originalVector B) := by
  rw [reducedMerge455Check, Integer.Sparse.eval_mergeBy, reducedTermEval462 B hB hF, reducedTermEval463 B hB hF]
  rw [originalMerge455, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval456 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge456 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge456 (originalVector B) := by
  rw [reducedMerge456Check, Integer.Sparse.eval_mergeBy, reducedMergeEval454 B hB hF, reducedMergeEval455 B hB hF]
  rw [originalMerge456, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge457 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge457 (originalVector B) := by
  rw [reducedMerge457Check, Integer.Sparse.eval_mergeBy, reducedMergeEval453 B hB hF, reducedMergeEval456 B hB hF]
  rw [originalMerge457, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge458 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge458 (originalVector B) := by
  rw [reducedMerge458Check, Integer.Sparse.eval_mergeBy, reducedMergeEval450 B hB hF, reducedMergeEval457 B hB hF]
  rw [originalMerge458, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge459 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge459 (originalVector B) := by
  rw [reducedMerge459Check, Integer.Sparse.eval_mergeBy, reducedTermEval465 B hB hF, reducedTermEval466 B hB hF]
  rw [originalMerge459, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge460 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge460 (originalVector B) := by
  rw [reducedMerge460Check, Integer.Sparse.eval_mergeBy, reducedTermEval464 B hB hF, reducedMergeEval459 B hB hF]
  rw [originalMerge460, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge461 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge461 (originalVector B) := by
  rw [reducedMerge461Check, Integer.Sparse.eval_mergeBy, reducedTermEval467 B hB hF, reducedTermEval468 B hB hF]
  rw [originalMerge461, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval462 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge462 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge462 (originalVector B) := by
  rw [reducedMerge462Check, Integer.Sparse.eval_mergeBy, reducedTermEval469 B hB hF, reducedTermEval470 B hB hF]
  rw [originalMerge462, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval463 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge463 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge463 (originalVector B) := by
  rw [reducedMerge463Check, Integer.Sparse.eval_mergeBy, reducedMergeEval461 B hB hF, reducedMergeEval462 B hB hF]
  rw [originalMerge463, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge464 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge464 (originalVector B) := by
  rw [reducedMerge464Check, Integer.Sparse.eval_mergeBy, reducedMergeEval460 B hB hF, reducedMergeEval463 B hB hF]
  rw [originalMerge464, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge465 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge465 (originalVector B) := by
  rw [reducedMerge465Check, Integer.Sparse.eval_mergeBy, reducedTermEval471 B hB hF, reducedTermEval472 B hB hF]
  rw [originalMerge465, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge466 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge466 (originalVector B) := by
  rw [reducedMerge466Check, Integer.Sparse.eval_mergeBy, reducedTermEval473 B hB hF, reducedTermEval474 B hB hF]
  rw [originalMerge466, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge467 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge467 (originalVector B) := by
  rw [reducedMerge467Check, Integer.Sparse.eval_mergeBy, reducedMergeEval465 B hB hF, reducedMergeEval466 B hB hF]
  rw [originalMerge467, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge468 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge468 (originalVector B) := by
  rw [reducedMerge468Check, Integer.Sparse.eval_mergeBy, reducedTermEval475 B hB hF, reducedTermEval476 B hB hF]
  rw [originalMerge468, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge469 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge469 (originalVector B) := by
  rw [reducedMerge469Check, Integer.Sparse.eval_mergeBy, reducedTermEval477 B hB hF, reducedTermEval478 B hB hF]
  rw [originalMerge469, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval470 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge470 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge470 (originalVector B) := by
  rw [reducedMerge470Check, Integer.Sparse.eval_mergeBy, reducedMergeEval468 B hB hF, reducedMergeEval469 B hB hF]
  rw [originalMerge470, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge471 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge471 (originalVector B) := by
  rw [reducedMerge471Check, Integer.Sparse.eval_mergeBy, reducedMergeEval467 B hB hF, reducedMergeEval470 B hB hF]
  rw [originalMerge471, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval472 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge472 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge472 (originalVector B) := by
  rw [reducedMerge472Check, Integer.Sparse.eval_mergeBy, reducedMergeEval464 B hB hF, reducedMergeEval471 B hB hF]
  rw [originalMerge472, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval473 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge473 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge473 (originalVector B) := by
  rw [reducedMerge473Check, Integer.Sparse.eval_mergeBy, reducedMergeEval458 B hB hF, reducedMergeEval472 B hB hF]
  rw [originalMerge473, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge474 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge474 (originalVector B) := by
  rw [reducedMerge474Check, Integer.Sparse.eval_mergeBy, reducedMergeEval444 B hB hF, reducedMergeEval473 B hB hF]
  rw [originalMerge474, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval475 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge475 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge475 (originalVector B) := by
  rw [reducedMerge475Check, Integer.Sparse.eval_mergeBy, reducedMergeEval415 B hB hF, reducedMergeEval474 B hB hF]
  rw [originalMerge475, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval476 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge476 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge476 (originalVector B) := by
  rw [reducedMerge476Check, Integer.Sparse.eval_mergeBy, reducedMergeEval356 B hB hF, reducedMergeEval475 B hB hF]
  rw [originalMerge476, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval477 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge477 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge477 (originalVector B) := by
  rw [reducedMerge477Check, Integer.Sparse.eval_mergeBy, reducedMergeEval237 B hB hF, reducedMergeEval476 B hB hF]
  rw [originalMerge477, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval478 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge478 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge478 (originalVector B) := by
  rw [reducedMerge478Check, Integer.Sparse.eval_mergeBy, reducedTermEval480 B hB hF, reducedTermEval481 B hB hF]
  rw [originalMerge478, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval479 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge479 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge479 (originalVector B) := by
  rw [reducedMerge479Check, Integer.Sparse.eval_mergeBy, reducedTermEval479 B hB hF, reducedMergeEval478 B hB hF]
  rw [originalMerge479, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
