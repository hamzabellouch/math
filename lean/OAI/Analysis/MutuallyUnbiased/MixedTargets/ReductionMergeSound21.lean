import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData21
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound20
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound21
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound22

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge672 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge672 (originalVector B) := by
  rw [reducedMerge672Check, Integer.Sparse.eval_mergeBy, reducedTermEval677 B hB hF, reducedTermEval678 B hB hF]
  rw [originalMerge672, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge673 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge673 (originalVector B) := by
  rw [reducedMerge673Check, Integer.Sparse.eval_mergeBy, reducedTermEval679 B hB hF, reducedTermEval680 B hB hF]
  rw [originalMerge673, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge674 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge674 (originalVector B) := by
  rw [reducedMerge674Check, Integer.Sparse.eval_mergeBy, reducedMergeEval672 B hB hF, reducedMergeEval673 B hB hF]
  rw [originalMerge674, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval675 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge675 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge675 (originalVector B) := by
  rw [reducedMerge675Check, Integer.Sparse.eval_mergeBy, reducedMergeEval671 B hB hF, reducedMergeEval674 B hB hF]
  rw [originalMerge675, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge676 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge676 (originalVector B) := by
  rw [reducedMerge676Check, Integer.Sparse.eval_mergeBy, reducedTermEval681 B hB hF, reducedTermEval682 B hB hF]
  rw [originalMerge676, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge677 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge677 (originalVector B) := by
  rw [reducedMerge677Check, Integer.Sparse.eval_mergeBy, reducedTermEval683 B hB hF, reducedTermEval684 B hB hF]
  rw [originalMerge677, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge678 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge678 (originalVector B) := by
  rw [reducedMerge678Check, Integer.Sparse.eval_mergeBy, reducedMergeEval676 B hB hF, reducedMergeEval677 B hB hF]
  rw [originalMerge678, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge679 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge679 (originalVector B) := by
  rw [reducedMerge679Check, Integer.Sparse.eval_mergeBy, reducedTermEval685 B hB hF, reducedTermEval686 B hB hF]
  rw [originalMerge679, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge680 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge680 (originalVector B) := by
  rw [reducedMerge680Check, Integer.Sparse.eval_mergeBy, reducedTermEval687 B hB hF, reducedTermEval688 B hB hF]
  rw [originalMerge680, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge681 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge681 (originalVector B) := by
  rw [reducedMerge681Check, Integer.Sparse.eval_mergeBy, reducedMergeEval679 B hB hF, reducedMergeEval680 B hB hF]
  rw [originalMerge681, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge682 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge682 (originalVector B) := by
  rw [reducedMerge682Check, Integer.Sparse.eval_mergeBy, reducedMergeEval678 B hB hF, reducedMergeEval681 B hB hF]
  rw [originalMerge682, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval683 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge683 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge683 (originalVector B) := by
  rw [reducedMerge683Check, Integer.Sparse.eval_mergeBy, reducedMergeEval675 B hB hF, reducedMergeEval682 B hB hF]
  rw [originalMerge683, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge684 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge684 (originalVector B) := by
  rw [reducedMerge684Check, Integer.Sparse.eval_mergeBy, reducedMergeEval669 B hB hF, reducedMergeEval683 B hB hF]
  rw [originalMerge684, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge685 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge685 (originalVector B) := by
  rw [reducedMerge685Check, Integer.Sparse.eval_mergeBy, reducedTermEval690 B hB hF, reducedTermEval691 B hB hF]
  rw [originalMerge685, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge686 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge686 (originalVector B) := by
  rw [reducedMerge686Check, Integer.Sparse.eval_mergeBy, reducedTermEval689 B hB hF, reducedMergeEval685 B hB hF]
  rw [originalMerge686, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge687 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge687 (originalVector B) := by
  rw [reducedMerge687Check, Integer.Sparse.eval_mergeBy, reducedTermEval692 B hB hF, reducedTermEval693 B hB hF]
  rw [originalMerge687, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge688 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge688 (originalVector B) := by
  rw [reducedMerge688Check, Integer.Sparse.eval_mergeBy, reducedTermEval694 B hB hF, reducedTermEval695 B hB hF]
  rw [originalMerge688, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge689 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge689 (originalVector B) := by
  rw [reducedMerge689Check, Integer.Sparse.eval_mergeBy, reducedMergeEval687 B hB hF, reducedMergeEval688 B hB hF]
  rw [originalMerge689, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge690 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge690 (originalVector B) := by
  rw [reducedMerge690Check, Integer.Sparse.eval_mergeBy, reducedMergeEval686 B hB hF, reducedMergeEval689 B hB hF]
  rw [originalMerge690, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge691 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge691 (originalVector B) := by
  rw [reducedMerge691Check, Integer.Sparse.eval_mergeBy, reducedTermEval696 B hB hF, reducedTermEval697 B hB hF]
  rw [originalMerge691, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge692 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge692 (originalVector B) := by
  rw [reducedMerge692Check, Integer.Sparse.eval_mergeBy, reducedTermEval698 B hB hF, reducedTermEval699 B hB hF]
  rw [originalMerge692, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge693 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge693 (originalVector B) := by
  rw [reducedMerge693Check, Integer.Sparse.eval_mergeBy, reducedMergeEval691 B hB hF, reducedMergeEval692 B hB hF]
  rw [originalMerge693, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval694 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge694 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge694 (originalVector B) := by
  rw [reducedMerge694Check, Integer.Sparse.eval_mergeBy, reducedTermEval700 B hB hF, reducedTermEval701 B hB hF]
  rw [originalMerge694, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge695 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge695 (originalVector B) := by
  rw [reducedMerge695Check, Integer.Sparse.eval_mergeBy, reducedTermEval702 B hB hF, reducedTermEval703 B hB hF]
  rw [originalMerge695, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge696 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge696 (originalVector B) := by
  rw [reducedMerge696Check, Integer.Sparse.eval_mergeBy, reducedMergeEval694 B hB hF, reducedMergeEval695 B hB hF]
  rw [originalMerge696, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge697 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge697 (originalVector B) := by
  rw [reducedMerge697Check, Integer.Sparse.eval_mergeBy, reducedMergeEval693 B hB hF, reducedMergeEval696 B hB hF]
  rw [originalMerge697, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval698 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge698 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge698 (originalVector B) := by
  rw [reducedMerge698Check, Integer.Sparse.eval_mergeBy, reducedMergeEval690 B hB hF, reducedMergeEval697 B hB hF]
  rw [originalMerge698, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval699 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge699 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge699 (originalVector B) := by
  rw [reducedMerge699Check, Integer.Sparse.eval_mergeBy, reducedTermEval705 B hB hF, reducedTermEval706 B hB hF]
  rw [originalMerge699, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval700 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge700 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge700 (originalVector B) := by
  rw [reducedMerge700Check, Integer.Sparse.eval_mergeBy, reducedTermEval704 B hB hF, reducedMergeEval699 B hB hF]
  rw [originalMerge700, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval701 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge701 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge701 (originalVector B) := by
  rw [reducedMerge701Check, Integer.Sparse.eval_mergeBy, reducedTermEval707 B hB hF, reducedTermEval708 B hB hF]
  rw [originalMerge701, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval702 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge702 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge702 (originalVector B) := by
  rw [reducedMerge702Check, Integer.Sparse.eval_mergeBy, reducedTermEval709 B hB hF, reducedTermEval710 B hB hF]
  rw [originalMerge702, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval703 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge703 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge703 (originalVector B) := by
  rw [reducedMerge703Check, Integer.Sparse.eval_mergeBy, reducedMergeEval701 B hB hF, reducedMergeEval702 B hB hF]
  rw [originalMerge703, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
