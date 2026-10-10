import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData20
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound19
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound20
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound21

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge640 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge640 (originalVector B) := by
  rw [reducedMerge640Check, Integer.Sparse.eval_mergeBy, reducedTermEval645 B hB hF, reducedTermEval646 B hB hF]
  rw [originalMerge640, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge641 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge641 (originalVector B) := by
  rw [reducedMerge641Check, Integer.Sparse.eval_mergeBy, reducedTermEval644 B hB hF, reducedMergeEval640 B hB hF]
  rw [originalMerge641, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge642 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge642 (originalVector B) := by
  rw [reducedMerge642Check, Integer.Sparse.eval_mergeBy, reducedTermEval647 B hB hF, reducedTermEval648 B hB hF]
  rw [originalMerge642, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge643 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge643 (originalVector B) := by
  rw [reducedMerge643Check, Integer.Sparse.eval_mergeBy, reducedTermEval649 B hB hF, reducedTermEval650 B hB hF]
  rw [originalMerge643, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge644 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge644 (originalVector B) := by
  rw [reducedMerge644Check, Integer.Sparse.eval_mergeBy, reducedMergeEval642 B hB hF, reducedMergeEval643 B hB hF]
  rw [originalMerge644, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge645 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge645 (originalVector B) := by
  rw [reducedMerge645Check, Integer.Sparse.eval_mergeBy, reducedMergeEval641 B hB hF, reducedMergeEval644 B hB hF]
  rw [originalMerge645, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge646 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge646 (originalVector B) := by
  rw [reducedMerge646Check, Integer.Sparse.eval_mergeBy, reducedTermEval651 B hB hF, reducedTermEval652 B hB hF]
  rw [originalMerge646, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge647 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge647 (originalVector B) := by
  rw [reducedMerge647Check, Integer.Sparse.eval_mergeBy, reducedTermEval653 B hB hF, reducedTermEval654 B hB hF]
  rw [originalMerge647, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval648 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge648 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge648 (originalVector B) := by
  rw [reducedMerge648Check, Integer.Sparse.eval_mergeBy, reducedMergeEval646 B hB hF, reducedMergeEval647 B hB hF]
  rw [originalMerge648, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval649 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge649 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge649 (originalVector B) := by
  rw [reducedMerge649Check, Integer.Sparse.eval_mergeBy, reducedTermEval655 B hB hF, reducedTermEval656 B hB hF]
  rw [originalMerge649, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge650 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge650 (originalVector B) := by
  rw [reducedMerge650Check, Integer.Sparse.eval_mergeBy, reducedTermEval657 B hB hF, reducedTermEval658 B hB hF]
  rw [originalMerge650, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval651 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge651 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge651 (originalVector B) := by
  rw [reducedMerge651Check, Integer.Sparse.eval_mergeBy, reducedMergeEval649 B hB hF, reducedMergeEval650 B hB hF]
  rw [originalMerge651, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge652 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge652 (originalVector B) := by
  rw [reducedMerge652Check, Integer.Sparse.eval_mergeBy, reducedMergeEval648 B hB hF, reducedMergeEval651 B hB hF]
  rw [originalMerge652, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval653 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge653 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge653 (originalVector B) := by
  rw [reducedMerge653Check, Integer.Sparse.eval_mergeBy, reducedMergeEval645 B hB hF, reducedMergeEval652 B hB hF]
  rw [originalMerge653, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge654 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge654 (originalVector B) := by
  rw [reducedMerge654Check, Integer.Sparse.eval_mergeBy, reducedMergeEval639 B hB hF, reducedMergeEval653 B hB hF]
  rw [originalMerge654, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge655 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge655 (originalVector B) := by
  rw [reducedMerge655Check, Integer.Sparse.eval_mergeBy, reducedMergeEval625 B hB hF, reducedMergeEval654 B hB hF]
  rw [originalMerge655, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval656 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge656 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge656 (originalVector B) := by
  rw [reducedMerge656Check, Integer.Sparse.eval_mergeBy, reducedTermEval660 B hB hF, reducedTermEval661 B hB hF]
  rw [originalMerge656, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval657 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge657 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge657 (originalVector B) := by
  rw [reducedMerge657Check, Integer.Sparse.eval_mergeBy, reducedTermEval659 B hB hF, reducedMergeEval656 B hB hF]
  rw [originalMerge657, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval658 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge658 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge658 (originalVector B) := by
  rw [reducedMerge658Check, Integer.Sparse.eval_mergeBy, reducedTermEval662 B hB hF, reducedTermEval663 B hB hF]
  rw [originalMerge658, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval659 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge659 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge659 (originalVector B) := by
  rw [reducedMerge659Check, Integer.Sparse.eval_mergeBy, reducedTermEval664 B hB hF, reducedTermEval665 B hB hF]
  rw [originalMerge659, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge660 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge660 (originalVector B) := by
  rw [reducedMerge660Check, Integer.Sparse.eval_mergeBy, reducedMergeEval658 B hB hF, reducedMergeEval659 B hB hF]
  rw [originalMerge660, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge661 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge661 (originalVector B) := by
  rw [reducedMerge661Check, Integer.Sparse.eval_mergeBy, reducedMergeEval657 B hB hF, reducedMergeEval660 B hB hF]
  rw [originalMerge661, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge662 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge662 (originalVector B) := by
  rw [reducedMerge662Check, Integer.Sparse.eval_mergeBy, reducedTermEval666 B hB hF, reducedTermEval667 B hB hF]
  rw [originalMerge662, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval663 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge663 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge663 (originalVector B) := by
  rw [reducedMerge663Check, Integer.Sparse.eval_mergeBy, reducedTermEval668 B hB hF, reducedTermEval669 B hB hF]
  rw [originalMerge663, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge664 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge664 (originalVector B) := by
  rw [reducedMerge664Check, Integer.Sparse.eval_mergeBy, reducedMergeEval662 B hB hF, reducedMergeEval663 B hB hF]
  rw [originalMerge664, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge665 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge665 (originalVector B) := by
  rw [reducedMerge665Check, Integer.Sparse.eval_mergeBy, reducedTermEval670 B hB hF, reducedTermEval671 B hB hF]
  rw [originalMerge665, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge666 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge666 (originalVector B) := by
  rw [reducedMerge666Check, Integer.Sparse.eval_mergeBy, reducedTermEval672 B hB hF, reducedTermEval673 B hB hF]
  rw [originalMerge666, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge667 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge667 (originalVector B) := by
  rw [reducedMerge667Check, Integer.Sparse.eval_mergeBy, reducedMergeEval665 B hB hF, reducedMergeEval666 B hB hF]
  rw [originalMerge667, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval668 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge668 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge668 (originalVector B) := by
  rw [reducedMerge668Check, Integer.Sparse.eval_mergeBy, reducedMergeEval664 B hB hF, reducedMergeEval667 B hB hF]
  rw [originalMerge668, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval669 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge669 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge669 (originalVector B) := by
  rw [reducedMerge669Check, Integer.Sparse.eval_mergeBy, reducedMergeEval661 B hB hF, reducedMergeEval668 B hB hF]
  rw [originalMerge669, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge670 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge670 (originalVector B) := by
  rw [reducedMerge670Check, Integer.Sparse.eval_mergeBy, reducedTermEval675 B hB hF, reducedTermEval676 B hB hF]
  rw [originalMerge670, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge671 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge671 (originalVector B) := by
  rw [reducedMerge671Check, Integer.Sparse.eval_mergeBy, reducedTermEval674 B hB hF, reducedMergeEval670 B hB hF]
  rw [originalMerge671, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
