import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData18
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound16
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound17
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound18
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound19

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge576 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge576 (originalVector B) := by
  rw [reducedMerge576Check, Integer.Sparse.eval_mergeBy, reducedTermEval582 B hB hF, reducedTermEval583 B hB hF]
  rw [originalMerge576, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval577 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge577 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge577 (originalVector B) := by
  rw [reducedMerge577Check, Integer.Sparse.eval_mergeBy, reducedMergeEval575 B hB hF, reducedMergeEval576 B hB hF]
  rw [originalMerge577, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval578 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge578 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge578 (originalVector B) := by
  rw [reducedMerge578Check, Integer.Sparse.eval_mergeBy, reducedMergeEval574 B hB hF, reducedMergeEval577 B hB hF]
  rw [originalMerge578, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval579 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge579 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge579 (originalVector B) := by
  rw [reducedMerge579Check, Integer.Sparse.eval_mergeBy, reducedMergeEval571 B hB hF, reducedMergeEval578 B hB hF]
  rw [originalMerge579, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval580 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge580 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge580 (originalVector B) := by
  rw [reducedMerge580Check, Integer.Sparse.eval_mergeBy, reducedTermEval585 B hB hF, reducedTermEval586 B hB hF]
  rw [originalMerge580, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval581 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge581 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge581 (originalVector B) := by
  rw [reducedMerge581Check, Integer.Sparse.eval_mergeBy, reducedTermEval584 B hB hF, reducedMergeEval580 B hB hF]
  rw [originalMerge581, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval582 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge582 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge582 (originalVector B) := by
  rw [reducedMerge582Check, Integer.Sparse.eval_mergeBy, reducedTermEval587 B hB hF, reducedTermEval588 B hB hF]
  rw [originalMerge582, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval583 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge583 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge583 (originalVector B) := by
  rw [reducedMerge583Check, Integer.Sparse.eval_mergeBy, reducedTermEval589 B hB hF, reducedTermEval590 B hB hF]
  rw [originalMerge583, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval584 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge584 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge584 (originalVector B) := by
  rw [reducedMerge584Check, Integer.Sparse.eval_mergeBy, reducedMergeEval582 B hB hF, reducedMergeEval583 B hB hF]
  rw [originalMerge584, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval585 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge585 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge585 (originalVector B) := by
  rw [reducedMerge585Check, Integer.Sparse.eval_mergeBy, reducedMergeEval581 B hB hF, reducedMergeEval584 B hB hF]
  rw [originalMerge585, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval586 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge586 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge586 (originalVector B) := by
  rw [reducedMerge586Check, Integer.Sparse.eval_mergeBy, reducedTermEval591 B hB hF, reducedTermEval592 B hB hF]
  rw [originalMerge586, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval587 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge587 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge587 (originalVector B) := by
  rw [reducedMerge587Check, Integer.Sparse.eval_mergeBy, reducedTermEval593 B hB hF, reducedTermEval594 B hB hF]
  rw [originalMerge587, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval588 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge588 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge588 (originalVector B) := by
  rw [reducedMerge588Check, Integer.Sparse.eval_mergeBy, reducedMergeEval586 B hB hF, reducedMergeEval587 B hB hF]
  rw [originalMerge588, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval589 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge589 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge589 (originalVector B) := by
  rw [reducedMerge589Check, Integer.Sparse.eval_mergeBy, reducedTermEval595 B hB hF, reducedTermEval596 B hB hF]
  rw [originalMerge589, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval590 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge590 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge590 (originalVector B) := by
  rw [reducedMerge590Check, Integer.Sparse.eval_mergeBy, reducedTermEval597 B hB hF, reducedTermEval598 B hB hF]
  rw [originalMerge590, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval591 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge591 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge591 (originalVector B) := by
  rw [reducedMerge591Check, Integer.Sparse.eval_mergeBy, reducedMergeEval589 B hB hF, reducedMergeEval590 B hB hF]
  rw [originalMerge591, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval592 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge592 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge592 (originalVector B) := by
  rw [reducedMerge592Check, Integer.Sparse.eval_mergeBy, reducedMergeEval588 B hB hF, reducedMergeEval591 B hB hF]
  rw [originalMerge592, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval593 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge593 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge593 (originalVector B) := by
  rw [reducedMerge593Check, Integer.Sparse.eval_mergeBy, reducedMergeEval585 B hB hF, reducedMergeEval592 B hB hF]
  rw [originalMerge593, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval594 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge594 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge594 (originalVector B) := by
  rw [reducedMerge594Check, Integer.Sparse.eval_mergeBy, reducedMergeEval579 B hB hF, reducedMergeEval593 B hB hF]
  rw [originalMerge594, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval595 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge595 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge595 (originalVector B) := by
  rw [reducedMerge595Check, Integer.Sparse.eval_mergeBy, reducedMergeEval565 B hB hF, reducedMergeEval594 B hB hF]
  rw [originalMerge595, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval596 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge596 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge596 (originalVector B) := by
  rw [reducedMerge596Check, Integer.Sparse.eval_mergeBy, reducedMergeEval536 B hB hF, reducedMergeEval595 B hB hF]
  rw [originalMerge596, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval597 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge597 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge597 (originalVector B) := by
  rw [reducedMerge597Check, Integer.Sparse.eval_mergeBy, reducedTermEval600 B hB hF, reducedTermEval601 B hB hF]
  rw [originalMerge597, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval598 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge598 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge598 (originalVector B) := by
  rw [reducedMerge598Check, Integer.Sparse.eval_mergeBy, reducedTermEval599 B hB hF, reducedMergeEval597 B hB hF]
  rw [originalMerge598, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval599 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge599 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge599 (originalVector B) := by
  rw [reducedMerge599Check, Integer.Sparse.eval_mergeBy, reducedTermEval602 B hB hF, reducedTermEval603 B hB hF]
  rw [originalMerge599, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval600 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge600 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge600 (originalVector B) := by
  rw [reducedMerge600Check, Integer.Sparse.eval_mergeBy, reducedTermEval604 B hB hF, reducedTermEval605 B hB hF]
  rw [originalMerge600, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge601 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge601 (originalVector B) := by
  rw [reducedMerge601Check, Integer.Sparse.eval_mergeBy, reducedMergeEval599 B hB hF, reducedMergeEval600 B hB hF]
  rw [originalMerge601, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge602 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge602 (originalVector B) := by
  rw [reducedMerge602Check, Integer.Sparse.eval_mergeBy, reducedMergeEval598 B hB hF, reducedMergeEval601 B hB hF]
  rw [originalMerge602, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge603 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge603 (originalVector B) := by
  rw [reducedMerge603Check, Integer.Sparse.eval_mergeBy, reducedTermEval606 B hB hF, reducedTermEval607 B hB hF]
  rw [originalMerge603, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge604 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge604 (originalVector B) := by
  rw [reducedMerge604Check, Integer.Sparse.eval_mergeBy, reducedTermEval608 B hB hF, reducedTermEval609 B hB hF]
  rw [originalMerge604, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge605 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge605 (originalVector B) := by
  rw [reducedMerge605Check, Integer.Sparse.eval_mergeBy, reducedMergeEval603 B hB hF, reducedMergeEval604 B hB hF]
  rw [originalMerge605, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge606 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge606 (originalVector B) := by
  rw [reducedMerge606Check, Integer.Sparse.eval_mergeBy, reducedTermEval610 B hB hF, reducedTermEval611 B hB hF]
  rw [originalMerge606, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval607 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge607 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge607 (originalVector B) := by
  rw [reducedMerge607Check, Integer.Sparse.eval_mergeBy, reducedTermEval612 B hB hF, reducedTermEval613 B hB hF]
  rw [originalMerge607, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
