import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData22
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound18
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound20
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound21
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound22
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound23

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval704 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge704 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge704 (originalVector B) := by
  rw [reducedMerge704Check, Integer.Sparse.eval_mergeBy, reducedMergeEval700 B hB hF, reducedMergeEval703 B hB hF]
  rw [originalMerge704, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval705 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge705 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge705 (originalVector B) := by
  rw [reducedMerge705Check, Integer.Sparse.eval_mergeBy, reducedTermEval711 B hB hF, reducedTermEval712 B hB hF]
  rw [originalMerge705, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval706 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge706 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge706 (originalVector B) := by
  rw [reducedMerge706Check, Integer.Sparse.eval_mergeBy, reducedTermEval713 B hB hF, reducedTermEval714 B hB hF]
  rw [originalMerge706, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval707 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge707 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge707 (originalVector B) := by
  rw [reducedMerge707Check, Integer.Sparse.eval_mergeBy, reducedMergeEval705 B hB hF, reducedMergeEval706 B hB hF]
  rw [originalMerge707, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval708 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge708 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge708 (originalVector B) := by
  rw [reducedMerge708Check, Integer.Sparse.eval_mergeBy, reducedTermEval715 B hB hF, reducedTermEval716 B hB hF]
  rw [originalMerge708, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval709 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge709 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge709 (originalVector B) := by
  rw [reducedMerge709Check, Integer.Sparse.eval_mergeBy, reducedTermEval717 B hB hF, reducedTermEval718 B hB hF]
  rw [originalMerge709, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval710 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge710 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge710 (originalVector B) := by
  rw [reducedMerge710Check, Integer.Sparse.eval_mergeBy, reducedMergeEval708 B hB hF, reducedMergeEval709 B hB hF]
  rw [originalMerge710, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval711 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge711 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge711 (originalVector B) := by
  rw [reducedMerge711Check, Integer.Sparse.eval_mergeBy, reducedMergeEval707 B hB hF, reducedMergeEval710 B hB hF]
  rw [originalMerge711, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge712 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge712 (originalVector B) := by
  rw [reducedMerge712Check, Integer.Sparse.eval_mergeBy, reducedMergeEval704 B hB hF, reducedMergeEval711 B hB hF]
  rw [originalMerge712, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval713 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge713 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge713 (originalVector B) := by
  rw [reducedMerge713Check, Integer.Sparse.eval_mergeBy, reducedMergeEval698 B hB hF, reducedMergeEval712 B hB hF]
  rw [originalMerge713, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge714 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge714 (originalVector B) := by
  rw [reducedMerge714Check, Integer.Sparse.eval_mergeBy, reducedMergeEval684 B hB hF, reducedMergeEval713 B hB hF]
  rw [originalMerge714, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge715 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge715 (originalVector B) := by
  rw [reducedMerge715Check, Integer.Sparse.eval_mergeBy, reducedMergeEval655 B hB hF, reducedMergeEval714 B hB hF]
  rw [originalMerge715, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval716 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge716 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge716 (originalVector B) := by
  rw [reducedMerge716Check, Integer.Sparse.eval_mergeBy, reducedMergeEval596 B hB hF, reducedMergeEval715 B hB hF]
  rw [originalMerge716, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval717 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge717 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge717 (originalVector B) := by
  rw [reducedMerge717Check, Integer.Sparse.eval_mergeBy, reducedTermEval720 B hB hF, reducedTermEval721 B hB hF]
  rw [originalMerge717, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval718 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge718 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge718 (originalVector B) := by
  rw [reducedMerge718Check, Integer.Sparse.eval_mergeBy, reducedTermEval719 B hB hF, reducedMergeEval717 B hB hF]
  rw [originalMerge718, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval719 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge719 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge719 (originalVector B) := by
  rw [reducedMerge719Check, Integer.Sparse.eval_mergeBy, reducedTermEval722 B hB hF, reducedTermEval723 B hB hF]
  rw [originalMerge719, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval720 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge720 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge720 (originalVector B) := by
  rw [reducedMerge720Check, Integer.Sparse.eval_mergeBy, reducedTermEval724 B hB hF, reducedTermEval725 B hB hF]
  rw [originalMerge720, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval721 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge721 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge721 (originalVector B) := by
  rw [reducedMerge721Check, Integer.Sparse.eval_mergeBy, reducedMergeEval719 B hB hF, reducedMergeEval720 B hB hF]
  rw [originalMerge721, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval722 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge722 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge722 (originalVector B) := by
  rw [reducedMerge722Check, Integer.Sparse.eval_mergeBy, reducedMergeEval718 B hB hF, reducedMergeEval721 B hB hF]
  rw [originalMerge722, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval723 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge723 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge723 (originalVector B) := by
  rw [reducedMerge723Check, Integer.Sparse.eval_mergeBy, reducedTermEval726 B hB hF, reducedTermEval727 B hB hF]
  rw [originalMerge723, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval724 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge724 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge724 (originalVector B) := by
  rw [reducedMerge724Check, Integer.Sparse.eval_mergeBy, reducedTermEval728 B hB hF, reducedTermEval729 B hB hF]
  rw [originalMerge724, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval725 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge725 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge725 (originalVector B) := by
  rw [reducedMerge725Check, Integer.Sparse.eval_mergeBy, reducedMergeEval723 B hB hF, reducedMergeEval724 B hB hF]
  rw [originalMerge725, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge726 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge726 (originalVector B) := by
  rw [reducedMerge726Check, Integer.Sparse.eval_mergeBy, reducedTermEval730 B hB hF, reducedTermEval731 B hB hF]
  rw [originalMerge726, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge727 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge727 (originalVector B) := by
  rw [reducedMerge727Check, Integer.Sparse.eval_mergeBy, reducedTermEval732 B hB hF, reducedTermEval733 B hB hF]
  rw [originalMerge727, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge728 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge728 (originalVector B) := by
  rw [reducedMerge728Check, Integer.Sparse.eval_mergeBy, reducedMergeEval726 B hB hF, reducedMergeEval727 B hB hF]
  rw [originalMerge728, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval729 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge729 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge729 (originalVector B) := by
  rw [reducedMerge729Check, Integer.Sparse.eval_mergeBy, reducedMergeEval725 B hB hF, reducedMergeEval728 B hB hF]
  rw [originalMerge729, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge730 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge730 (originalVector B) := by
  rw [reducedMerge730Check, Integer.Sparse.eval_mergeBy, reducedMergeEval722 B hB hF, reducedMergeEval729 B hB hF]
  rw [originalMerge730, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval731 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge731 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge731 (originalVector B) := by
  rw [reducedMerge731Check, Integer.Sparse.eval_mergeBy, reducedTermEval735 B hB hF, reducedTermEval736 B hB hF]
  rw [originalMerge731, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval732 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge732 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge732 (originalVector B) := by
  rw [reducedMerge732Check, Integer.Sparse.eval_mergeBy, reducedTermEval734 B hB hF, reducedMergeEval731 B hB hF]
  rw [originalMerge732, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval733 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge733 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge733 (originalVector B) := by
  rw [reducedMerge733Check, Integer.Sparse.eval_mergeBy, reducedTermEval737 B hB hF, reducedTermEval738 B hB hF]
  rw [originalMerge733, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval734 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge734 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge734 (originalVector B) := by
  rw [reducedMerge734Check, Integer.Sparse.eval_mergeBy, reducedTermEval739 B hB hF, reducedTermEval740 B hB hF]
  rw [originalMerge734, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval735 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge735 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge735 (originalVector B) := by
  rw [reducedMerge735Check, Integer.Sparse.eval_mergeBy, reducedMergeEval733 B hB hF, reducedMergeEval734 B hB hF]
  rw [originalMerge735, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
