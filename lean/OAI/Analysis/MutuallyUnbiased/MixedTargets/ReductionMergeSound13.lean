import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData13
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound13
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound14

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval416 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge416 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge416 (originalVector B) := by
  rw [reducedMerge416Check, Integer.Sparse.eval_mergeBy, reducedTermEval420 B hB hF, reducedTermEval421 B hB hF]
  rw [originalMerge416, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval417 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge417 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge417 (originalVector B) := by
  rw [reducedMerge417Check, Integer.Sparse.eval_mergeBy, reducedTermEval419 B hB hF, reducedMergeEval416 B hB hF]
  rw [originalMerge417, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval418 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge418 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge418 (originalVector B) := by
  rw [reducedMerge418Check, Integer.Sparse.eval_mergeBy, reducedTermEval422 B hB hF, reducedTermEval423 B hB hF]
  rw [originalMerge418, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval419 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge419 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge419 (originalVector B) := by
  rw [reducedMerge419Check, Integer.Sparse.eval_mergeBy, reducedTermEval424 B hB hF, reducedTermEval425 B hB hF]
  rw [originalMerge419, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval420 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge420 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge420 (originalVector B) := by
  rw [reducedMerge420Check, Integer.Sparse.eval_mergeBy, reducedMergeEval418 B hB hF, reducedMergeEval419 B hB hF]
  rw [originalMerge420, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval421 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge421 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge421 (originalVector B) := by
  rw [reducedMerge421Check, Integer.Sparse.eval_mergeBy, reducedMergeEval417 B hB hF, reducedMergeEval420 B hB hF]
  rw [originalMerge421, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge422 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge422 (originalVector B) := by
  rw [reducedMerge422Check, Integer.Sparse.eval_mergeBy, reducedTermEval426 B hB hF, reducedTermEval427 B hB hF]
  rw [originalMerge422, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge423 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge423 (originalVector B) := by
  rw [reducedMerge423Check, Integer.Sparse.eval_mergeBy, reducedTermEval428 B hB hF, reducedTermEval429 B hB hF]
  rw [originalMerge423, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge424 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge424 (originalVector B) := by
  rw [reducedMerge424Check, Integer.Sparse.eval_mergeBy, reducedMergeEval422 B hB hF, reducedMergeEval423 B hB hF]
  rw [originalMerge424, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval425 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge425 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge425 (originalVector B) := by
  rw [reducedMerge425Check, Integer.Sparse.eval_mergeBy, reducedTermEval430 B hB hF, reducedTermEval431 B hB hF]
  rw [originalMerge425, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge426 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge426 (originalVector B) := by
  rw [reducedMerge426Check, Integer.Sparse.eval_mergeBy, reducedTermEval432 B hB hF, reducedTermEval433 B hB hF]
  rw [originalMerge426, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge427 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge427 (originalVector B) := by
  rw [reducedMerge427Check, Integer.Sparse.eval_mergeBy, reducedMergeEval425 B hB hF, reducedMergeEval426 B hB hF]
  rw [originalMerge427, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval428 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge428 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge428 (originalVector B) := by
  rw [reducedMerge428Check, Integer.Sparse.eval_mergeBy, reducedMergeEval424 B hB hF, reducedMergeEval427 B hB hF]
  rw [originalMerge428, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval429 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge429 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge429 (originalVector B) := by
  rw [reducedMerge429Check, Integer.Sparse.eval_mergeBy, reducedMergeEval421 B hB hF, reducedMergeEval428 B hB hF]
  rw [originalMerge429, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval430 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge430 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge430 (originalVector B) := by
  rw [reducedMerge430Check, Integer.Sparse.eval_mergeBy, reducedTermEval435 B hB hF, reducedTermEval436 B hB hF]
  rw [originalMerge430, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval431 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge431 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge431 (originalVector B) := by
  rw [reducedMerge431Check, Integer.Sparse.eval_mergeBy, reducedTermEval434 B hB hF, reducedMergeEval430 B hB hF]
  rw [originalMerge431, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge432 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge432 (originalVector B) := by
  rw [reducedMerge432Check, Integer.Sparse.eval_mergeBy, reducedTermEval437 B hB hF, reducedTermEval438 B hB hF]
  rw [originalMerge432, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge433 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge433 (originalVector B) := by
  rw [reducedMerge433Check, Integer.Sparse.eval_mergeBy, reducedTermEval439 B hB hF, reducedTermEval440 B hB hF]
  rw [originalMerge433, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval434 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge434 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge434 (originalVector B) := by
  rw [reducedMerge434Check, Integer.Sparse.eval_mergeBy, reducedMergeEval432 B hB hF, reducedMergeEval433 B hB hF]
  rw [originalMerge434, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge435 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge435 (originalVector B) := by
  rw [reducedMerge435Check, Integer.Sparse.eval_mergeBy, reducedMergeEval431 B hB hF, reducedMergeEval434 B hB hF]
  rw [originalMerge435, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval436 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge436 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge436 (originalVector B) := by
  rw [reducedMerge436Check, Integer.Sparse.eval_mergeBy, reducedTermEval441 B hB hF, reducedTermEval442 B hB hF]
  rw [originalMerge436, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval437 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge437 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge437 (originalVector B) := by
  rw [reducedMerge437Check, Integer.Sparse.eval_mergeBy, reducedTermEval443 B hB hF, reducedTermEval444 B hB hF]
  rw [originalMerge437, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval438 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge438 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge438 (originalVector B) := by
  rw [reducedMerge438Check, Integer.Sparse.eval_mergeBy, reducedMergeEval436 B hB hF, reducedMergeEval437 B hB hF]
  rw [originalMerge438, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge439 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge439 (originalVector B) := by
  rw [reducedMerge439Check, Integer.Sparse.eval_mergeBy, reducedTermEval445 B hB hF, reducedTermEval446 B hB hF]
  rw [originalMerge439, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge440 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge440 (originalVector B) := by
  rw [reducedMerge440Check, Integer.Sparse.eval_mergeBy, reducedTermEval447 B hB hF, reducedTermEval448 B hB hF]
  rw [originalMerge440, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge441 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge441 (originalVector B) := by
  rw [reducedMerge441Check, Integer.Sparse.eval_mergeBy, reducedMergeEval439 B hB hF, reducedMergeEval440 B hB hF]
  rw [originalMerge441, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge442 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge442 (originalVector B) := by
  rw [reducedMerge442Check, Integer.Sparse.eval_mergeBy, reducedMergeEval438 B hB hF, reducedMergeEval441 B hB hF]
  rw [originalMerge442, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge443 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge443 (originalVector B) := by
  rw [reducedMerge443Check, Integer.Sparse.eval_mergeBy, reducedMergeEval435 B hB hF, reducedMergeEval442 B hB hF]
  rw [originalMerge443, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval444 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge444 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge444 (originalVector B) := by
  rw [reducedMerge444Check, Integer.Sparse.eval_mergeBy, reducedMergeEval429 B hB hF, reducedMergeEval443 B hB hF]
  rw [originalMerge444, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval445 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge445 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge445 (originalVector B) := by
  rw [reducedMerge445Check, Integer.Sparse.eval_mergeBy, reducedTermEval450 B hB hF, reducedTermEval451 B hB hF]
  rw [originalMerge445, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval446 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge446 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge446 (originalVector B) := by
  rw [reducedMerge446Check, Integer.Sparse.eval_mergeBy, reducedTermEval449 B hB hF, reducedMergeEval445 B hB hF]
  rw [originalMerge446, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval447 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge447 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge447 (originalVector B) := by
  rw [reducedMerge447Check, Integer.Sparse.eval_mergeBy, reducedTermEval452 B hB hF, reducedTermEval453 B hB hF]
  rw [originalMerge447, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
