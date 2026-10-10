import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData12
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound11
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound12
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound13

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval384 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge384 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge384 (originalVector B) := by
  rw [reducedMerge384Check, Integer.Sparse.eval_mergeBy, reducedMergeEval376 B hB hF, reducedMergeEval383 B hB hF]
  rw [originalMerge384, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval385 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge385 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge385 (originalVector B) := by
  rw [reducedMerge385Check, Integer.Sparse.eval_mergeBy, reducedMergeEval370 B hB hF, reducedMergeEval384 B hB hF]
  rw [originalMerge385, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval386 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge386 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge386 (originalVector B) := by
  rw [reducedMerge386Check, Integer.Sparse.eval_mergeBy, reducedTermEval390 B hB hF, reducedTermEval391 B hB hF]
  rw [originalMerge386, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval387 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge387 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge387 (originalVector B) := by
  rw [reducedMerge387Check, Integer.Sparse.eval_mergeBy, reducedTermEval389 B hB hF, reducedMergeEval386 B hB hF]
  rw [originalMerge387, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval388 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge388 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge388 (originalVector B) := by
  rw [reducedMerge388Check, Integer.Sparse.eval_mergeBy, reducedTermEval392 B hB hF, reducedTermEval393 B hB hF]
  rw [originalMerge388, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge389 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge389 (originalVector B) := by
  rw [reducedMerge389Check, Integer.Sparse.eval_mergeBy, reducedTermEval394 B hB hF, reducedTermEval395 B hB hF]
  rw [originalMerge389, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval390 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge390 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge390 (originalVector B) := by
  rw [reducedMerge390Check, Integer.Sparse.eval_mergeBy, reducedMergeEval388 B hB hF, reducedMergeEval389 B hB hF]
  rw [originalMerge390, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval391 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge391 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge391 (originalVector B) := by
  rw [reducedMerge391Check, Integer.Sparse.eval_mergeBy, reducedMergeEval387 B hB hF, reducedMergeEval390 B hB hF]
  rw [originalMerge391, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval392 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge392 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge392 (originalVector B) := by
  rw [reducedMerge392Check, Integer.Sparse.eval_mergeBy, reducedTermEval396 B hB hF, reducedTermEval397 B hB hF]
  rw [originalMerge392, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval393 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge393 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge393 (originalVector B) := by
  rw [reducedMerge393Check, Integer.Sparse.eval_mergeBy, reducedTermEval398 B hB hF, reducedTermEval399 B hB hF]
  rw [originalMerge393, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge394 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge394 (originalVector B) := by
  rw [reducedMerge394Check, Integer.Sparse.eval_mergeBy, reducedMergeEval392 B hB hF, reducedMergeEval393 B hB hF]
  rw [originalMerge394, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval395 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge395 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge395 (originalVector B) := by
  rw [reducedMerge395Check, Integer.Sparse.eval_mergeBy, reducedTermEval400 B hB hF, reducedTermEval401 B hB hF]
  rw [originalMerge395, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge396 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge396 (originalVector B) := by
  rw [reducedMerge396Check, Integer.Sparse.eval_mergeBy, reducedTermEval402 B hB hF, reducedTermEval403 B hB hF]
  rw [originalMerge396, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval397 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge397 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge397 (originalVector B) := by
  rw [reducedMerge397Check, Integer.Sparse.eval_mergeBy, reducedMergeEval395 B hB hF, reducedMergeEval396 B hB hF]
  rw [originalMerge397, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval398 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge398 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge398 (originalVector B) := by
  rw [reducedMerge398Check, Integer.Sparse.eval_mergeBy, reducedMergeEval394 B hB hF, reducedMergeEval397 B hB hF]
  rw [originalMerge398, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval399 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge399 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge399 (originalVector B) := by
  rw [reducedMerge399Check, Integer.Sparse.eval_mergeBy, reducedMergeEval391 B hB hF, reducedMergeEval398 B hB hF]
  rw [originalMerge399, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval400 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge400 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge400 (originalVector B) := by
  rw [reducedMerge400Check, Integer.Sparse.eval_mergeBy, reducedTermEval405 B hB hF, reducedTermEval406 B hB hF]
  rw [originalMerge400, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval401 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge401 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge401 (originalVector B) := by
  rw [reducedMerge401Check, Integer.Sparse.eval_mergeBy, reducedTermEval404 B hB hF, reducedMergeEval400 B hB hF]
  rw [originalMerge401, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge402 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge402 (originalVector B) := by
  rw [reducedMerge402Check, Integer.Sparse.eval_mergeBy, reducedTermEval407 B hB hF, reducedTermEval408 B hB hF]
  rw [originalMerge402, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge403 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge403 (originalVector B) := by
  rw [reducedMerge403Check, Integer.Sparse.eval_mergeBy, reducedTermEval409 B hB hF, reducedTermEval410 B hB hF]
  rw [originalMerge403, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval404 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge404 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge404 (originalVector B) := by
  rw [reducedMerge404Check, Integer.Sparse.eval_mergeBy, reducedMergeEval402 B hB hF, reducedMergeEval403 B hB hF]
  rw [originalMerge404, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval405 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge405 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge405 (originalVector B) := by
  rw [reducedMerge405Check, Integer.Sparse.eval_mergeBy, reducedMergeEval401 B hB hF, reducedMergeEval404 B hB hF]
  rw [originalMerge405, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval406 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge406 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge406 (originalVector B) := by
  rw [reducedMerge406Check, Integer.Sparse.eval_mergeBy, reducedTermEval411 B hB hF, reducedTermEval412 B hB hF]
  rw [originalMerge406, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval407 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge407 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge407 (originalVector B) := by
  rw [reducedMerge407Check, Integer.Sparse.eval_mergeBy, reducedTermEval413 B hB hF, reducedTermEval414 B hB hF]
  rw [originalMerge407, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge408 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge408 (originalVector B) := by
  rw [reducedMerge408Check, Integer.Sparse.eval_mergeBy, reducedMergeEval406 B hB hF, reducedMergeEval407 B hB hF]
  rw [originalMerge408, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge409 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge409 (originalVector B) := by
  rw [reducedMerge409Check, Integer.Sparse.eval_mergeBy, reducedTermEval415 B hB hF, reducedTermEval416 B hB hF]
  rw [originalMerge409, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge410 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge410 (originalVector B) := by
  rw [reducedMerge410Check, Integer.Sparse.eval_mergeBy, reducedTermEval417 B hB hF, reducedTermEval418 B hB hF]
  rw [originalMerge410, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval411 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge411 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge411 (originalVector B) := by
  rw [reducedMerge411Check, Integer.Sparse.eval_mergeBy, reducedMergeEval409 B hB hF, reducedMergeEval410 B hB hF]
  rw [originalMerge411, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval412 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge412 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge412 (originalVector B) := by
  rw [reducedMerge412Check, Integer.Sparse.eval_mergeBy, reducedMergeEval408 B hB hF, reducedMergeEval411 B hB hF]
  rw [originalMerge412, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval413 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge413 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge413 (originalVector B) := by
  rw [reducedMerge413Check, Integer.Sparse.eval_mergeBy, reducedMergeEval405 B hB hF, reducedMergeEval412 B hB hF]
  rw [originalMerge413, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval414 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge414 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge414 (originalVector B) := by
  rw [reducedMerge414Check, Integer.Sparse.eval_mergeBy, reducedMergeEval399 B hB hF, reducedMergeEval413 B hB hF]
  rw [originalMerge414, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge415 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge415 (originalVector B) := by
  rw [reducedMerge415Check, Integer.Sparse.eval_mergeBy, reducedMergeEval385 B hB hF, reducedMergeEval414 B hB hF]
  rw [originalMerge415, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
