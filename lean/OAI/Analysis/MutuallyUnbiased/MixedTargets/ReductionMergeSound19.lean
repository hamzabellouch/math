import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData19
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound18
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound19
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound20

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge608 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge608 (originalVector B) := by
  rw [reducedMerge608Check, Integer.Sparse.eval_mergeBy, reducedMergeEval606 B hB hF, reducedMergeEval607 B hB hF]
  rw [originalMerge608, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge609 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge609 (originalVector B) := by
  rw [reducedMerge609Check, Integer.Sparse.eval_mergeBy, reducedMergeEval605 B hB hF, reducedMergeEval608 B hB hF]
  rw [originalMerge609, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge610 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge610 (originalVector B) := by
  rw [reducedMerge610Check, Integer.Sparse.eval_mergeBy, reducedMergeEval602 B hB hF, reducedMergeEval609 B hB hF]
  rw [originalMerge610, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge611 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge611 (originalVector B) := by
  rw [reducedMerge611Check, Integer.Sparse.eval_mergeBy, reducedTermEval615 B hB hF, reducedTermEval616 B hB hF]
  rw [originalMerge611, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge612 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge612 (originalVector B) := by
  rw [reducedMerge612Check, Integer.Sparse.eval_mergeBy, reducedTermEval614 B hB hF, reducedMergeEval611 B hB hF]
  rw [originalMerge612, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge613 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge613 (originalVector B) := by
  rw [reducedMerge613Check, Integer.Sparse.eval_mergeBy, reducedTermEval617 B hB hF, reducedTermEval618 B hB hF]
  rw [originalMerge613, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge614 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge614 (originalVector B) := by
  rw [reducedMerge614Check, Integer.Sparse.eval_mergeBy, reducedTermEval619 B hB hF, reducedTermEval620 B hB hF]
  rw [originalMerge614, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge615 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge615 (originalVector B) := by
  rw [reducedMerge615Check, Integer.Sparse.eval_mergeBy, reducedMergeEval613 B hB hF, reducedMergeEval614 B hB hF]
  rw [originalMerge615, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge616 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge616 (originalVector B) := by
  rw [reducedMerge616Check, Integer.Sparse.eval_mergeBy, reducedMergeEval612 B hB hF, reducedMergeEval615 B hB hF]
  rw [originalMerge616, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge617 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge617 (originalVector B) := by
  rw [reducedMerge617Check, Integer.Sparse.eval_mergeBy, reducedTermEval621 B hB hF, reducedTermEval622 B hB hF]
  rw [originalMerge617, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge618 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge618 (originalVector B) := by
  rw [reducedMerge618Check, Integer.Sparse.eval_mergeBy, reducedTermEval623 B hB hF, reducedTermEval624 B hB hF]
  rw [originalMerge618, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge619 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge619 (originalVector B) := by
  rw [reducedMerge619Check, Integer.Sparse.eval_mergeBy, reducedMergeEval617 B hB hF, reducedMergeEval618 B hB hF]
  rw [originalMerge619, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge620 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge620 (originalVector B) := by
  rw [reducedMerge620Check, Integer.Sparse.eval_mergeBy, reducedTermEval625 B hB hF, reducedTermEval626 B hB hF]
  rw [originalMerge620, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge621 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge621 (originalVector B) := by
  rw [reducedMerge621Check, Integer.Sparse.eval_mergeBy, reducedTermEval627 B hB hF, reducedTermEval628 B hB hF]
  rw [originalMerge621, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge622 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge622 (originalVector B) := by
  rw [reducedMerge622Check, Integer.Sparse.eval_mergeBy, reducedMergeEval620 B hB hF, reducedMergeEval621 B hB hF]
  rw [originalMerge622, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge623 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge623 (originalVector B) := by
  rw [reducedMerge623Check, Integer.Sparse.eval_mergeBy, reducedMergeEval619 B hB hF, reducedMergeEval622 B hB hF]
  rw [originalMerge623, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge624 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge624 (originalVector B) := by
  rw [reducedMerge624Check, Integer.Sparse.eval_mergeBy, reducedMergeEval616 B hB hF, reducedMergeEval623 B hB hF]
  rw [originalMerge624, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge625 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge625 (originalVector B) := by
  rw [reducedMerge625Check, Integer.Sparse.eval_mergeBy, reducedMergeEval610 B hB hF, reducedMergeEval624 B hB hF]
  rw [originalMerge625, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge626 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge626 (originalVector B) := by
  rw [reducedMerge626Check, Integer.Sparse.eval_mergeBy, reducedTermEval630 B hB hF, reducedTermEval631 B hB hF]
  rw [originalMerge626, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge627 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge627 (originalVector B) := by
  rw [reducedMerge627Check, Integer.Sparse.eval_mergeBy, reducedTermEval629 B hB hF, reducedMergeEval626 B hB hF]
  rw [originalMerge627, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge628 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge628 (originalVector B) := by
  rw [reducedMerge628Check, Integer.Sparse.eval_mergeBy, reducedTermEval632 B hB hF, reducedTermEval633 B hB hF]
  rw [originalMerge628, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge629 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge629 (originalVector B) := by
  rw [reducedMerge629Check, Integer.Sparse.eval_mergeBy, reducedTermEval634 B hB hF, reducedTermEval635 B hB hF]
  rw [originalMerge629, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval630 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge630 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge630 (originalVector B) := by
  rw [reducedMerge630Check, Integer.Sparse.eval_mergeBy, reducedMergeEval628 B hB hF, reducedMergeEval629 B hB hF]
  rw [originalMerge630, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval631 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge631 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge631 (originalVector B) := by
  rw [reducedMerge631Check, Integer.Sparse.eval_mergeBy, reducedMergeEval627 B hB hF, reducedMergeEval630 B hB hF]
  rw [originalMerge631, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval632 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge632 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge632 (originalVector B) := by
  rw [reducedMerge632Check, Integer.Sparse.eval_mergeBy, reducedTermEval636 B hB hF, reducedTermEval637 B hB hF]
  rw [originalMerge632, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval633 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge633 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge633 (originalVector B) := by
  rw [reducedMerge633Check, Integer.Sparse.eval_mergeBy, reducedTermEval638 B hB hF, reducedTermEval639 B hB hF]
  rw [originalMerge633, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval634 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge634 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge634 (originalVector B) := by
  rw [reducedMerge634Check, Integer.Sparse.eval_mergeBy, reducedMergeEval632 B hB hF, reducedMergeEval633 B hB hF]
  rw [originalMerge634, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge635 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge635 (originalVector B) := by
  rw [reducedMerge635Check, Integer.Sparse.eval_mergeBy, reducedTermEval640 B hB hF, reducedTermEval641 B hB hF]
  rw [originalMerge635, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge636 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge636 (originalVector B) := by
  rw [reducedMerge636Check, Integer.Sparse.eval_mergeBy, reducedTermEval642 B hB hF, reducedTermEval643 B hB hF]
  rw [originalMerge636, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge637 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge637 (originalVector B) := by
  rw [reducedMerge637Check, Integer.Sparse.eval_mergeBy, reducedMergeEval635 B hB hF, reducedMergeEval636 B hB hF]
  rw [originalMerge637, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval638 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge638 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge638 (originalVector B) := by
  rw [reducedMerge638Check, Integer.Sparse.eval_mergeBy, reducedMergeEval634 B hB hF, reducedMergeEval637 B hB hF]
  rw [originalMerge638, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval639 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge639 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge639 (originalVector B) := by
  rw [reducedMerge639Check, Integer.Sparse.eval_mergeBy, reducedMergeEval631 B hB hF, reducedMergeEval638 B hB hF]
  rw [originalMerge639, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
