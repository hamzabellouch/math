import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData25
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound24
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound25
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound26

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval800 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge800 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge800 (originalVector B) := by
  rw [reducedMerge800Check, Integer.Sparse.eval_mergeBy, reducedTermEval807 B hB hF, reducedTermEval808 B hB hF]
  rw [originalMerge800, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval801 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge801 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge801 (originalVector B) := by
  rw [reducedMerge801Check, Integer.Sparse.eval_mergeBy, reducedMergeEval799 B hB hF, reducedMergeEval800 B hB hF]
  rw [originalMerge801, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval802 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge802 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge802 (originalVector B) := by
  rw [reducedMerge802Check, Integer.Sparse.eval_mergeBy, reducedMergeEval798 B hB hF, reducedMergeEval801 B hB hF]
  rw [originalMerge802, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge803 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge803 (originalVector B) := by
  rw [reducedMerge803Check, Integer.Sparse.eval_mergeBy, reducedMergeEval795 B hB hF, reducedMergeEval802 B hB hF]
  rw [originalMerge803, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval804 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge804 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge804 (originalVector B) := by
  rw [reducedMerge804Check, Integer.Sparse.eval_mergeBy, reducedMergeEval789 B hB hF, reducedMergeEval803 B hB hF]
  rw [originalMerge804, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge805 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge805 (originalVector B) := by
  rw [reducedMerge805Check, Integer.Sparse.eval_mergeBy, reducedTermEval810 B hB hF, reducedTermEval811 B hB hF]
  rw [originalMerge805, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge806 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge806 (originalVector B) := by
  rw [reducedMerge806Check, Integer.Sparse.eval_mergeBy, reducedTermEval809 B hB hF, reducedMergeEval805 B hB hF]
  rw [originalMerge806, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge807 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge807 (originalVector B) := by
  rw [reducedMerge807Check, Integer.Sparse.eval_mergeBy, reducedTermEval812 B hB hF, reducedTermEval813 B hB hF]
  rw [originalMerge807, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge808 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge808 (originalVector B) := by
  rw [reducedMerge808Check, Integer.Sparse.eval_mergeBy, reducedTermEval814 B hB hF, reducedTermEval815 B hB hF]
  rw [originalMerge808, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge809 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge809 (originalVector B) := by
  rw [reducedMerge809Check, Integer.Sparse.eval_mergeBy, reducedMergeEval807 B hB hF, reducedMergeEval808 B hB hF]
  rw [originalMerge809, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge810 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge810 (originalVector B) := by
  rw [reducedMerge810Check, Integer.Sparse.eval_mergeBy, reducedMergeEval806 B hB hF, reducedMergeEval809 B hB hF]
  rw [originalMerge810, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval811 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge811 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge811 (originalVector B) := by
  rw [reducedMerge811Check, Integer.Sparse.eval_mergeBy, reducedTermEval816 B hB hF, reducedTermEval817 B hB hF]
  rw [originalMerge811, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge812 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge812 (originalVector B) := by
  rw [reducedMerge812Check, Integer.Sparse.eval_mergeBy, reducedTermEval818 B hB hF, reducedTermEval819 B hB hF]
  rw [originalMerge812, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval813 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge813 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge813 (originalVector B) := by
  rw [reducedMerge813Check, Integer.Sparse.eval_mergeBy, reducedMergeEval811 B hB hF, reducedMergeEval812 B hB hF]
  rw [originalMerge813, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge814 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge814 (originalVector B) := by
  rw [reducedMerge814Check, Integer.Sparse.eval_mergeBy, reducedTermEval820 B hB hF, reducedTermEval821 B hB hF]
  rw [originalMerge814, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval815 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge815 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge815 (originalVector B) := by
  rw [reducedMerge815Check, Integer.Sparse.eval_mergeBy, reducedTermEval822 B hB hF, reducedTermEval823 B hB hF]
  rw [originalMerge815, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge816 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge816 (originalVector B) := by
  rw [reducedMerge816Check, Integer.Sparse.eval_mergeBy, reducedMergeEval814 B hB hF, reducedMergeEval815 B hB hF]
  rw [originalMerge816, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge817 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge817 (originalVector B) := by
  rw [reducedMerge817Check, Integer.Sparse.eval_mergeBy, reducedMergeEval813 B hB hF, reducedMergeEval816 B hB hF]
  rw [originalMerge817, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge818 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge818 (originalVector B) := by
  rw [reducedMerge818Check, Integer.Sparse.eval_mergeBy, reducedMergeEval810 B hB hF, reducedMergeEval817 B hB hF]
  rw [originalMerge818, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge819 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge819 (originalVector B) := by
  rw [reducedMerge819Check, Integer.Sparse.eval_mergeBy, reducedTermEval825 B hB hF, reducedTermEval826 B hB hF]
  rw [originalMerge819, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge820 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge820 (originalVector B) := by
  rw [reducedMerge820Check, Integer.Sparse.eval_mergeBy, reducedTermEval824 B hB hF, reducedMergeEval819 B hB hF]
  rw [originalMerge820, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge821 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge821 (originalVector B) := by
  rw [reducedMerge821Check, Integer.Sparse.eval_mergeBy, reducedTermEval827 B hB hF, reducedTermEval828 B hB hF]
  rw [originalMerge821, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval822 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge822 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge822 (originalVector B) := by
  rw [reducedMerge822Check, Integer.Sparse.eval_mergeBy, reducedTermEval829 B hB hF, reducedTermEval830 B hB hF]
  rw [originalMerge822, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge823 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge823 (originalVector B) := by
  rw [reducedMerge823Check, Integer.Sparse.eval_mergeBy, reducedMergeEval821 B hB hF, reducedMergeEval822 B hB hF]
  rw [originalMerge823, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge824 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge824 (originalVector B) := by
  rw [reducedMerge824Check, Integer.Sparse.eval_mergeBy, reducedMergeEval820 B hB hF, reducedMergeEval823 B hB hF]
  rw [originalMerge824, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval825 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge825 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge825 (originalVector B) := by
  rw [reducedMerge825Check, Integer.Sparse.eval_mergeBy, reducedTermEval831 B hB hF, reducedTermEval832 B hB hF]
  rw [originalMerge825, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval826 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge826 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge826 (originalVector B) := by
  rw [reducedMerge826Check, Integer.Sparse.eval_mergeBy, reducedTermEval833 B hB hF, reducedTermEval834 B hB hF]
  rw [originalMerge826, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge827 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge827 (originalVector B) := by
  rw [reducedMerge827Check, Integer.Sparse.eval_mergeBy, reducedMergeEval825 B hB hF, reducedMergeEval826 B hB hF]
  rw [originalMerge827, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval828 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge828 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge828 (originalVector B) := by
  rw [reducedMerge828Check, Integer.Sparse.eval_mergeBy, reducedTermEval835 B hB hF, reducedTermEval836 B hB hF]
  rw [originalMerge828, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge829 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge829 (originalVector B) := by
  rw [reducedMerge829Check, Integer.Sparse.eval_mergeBy, reducedTermEval837 B hB hF, reducedTermEval838 B hB hF]
  rw [originalMerge829, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge830 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge830 (originalVector B) := by
  rw [reducedMerge830Check, Integer.Sparse.eval_mergeBy, reducedMergeEval828 B hB hF, reducedMergeEval829 B hB hF]
  rw [originalMerge830, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval831 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge831 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge831 (originalVector B) := by
  rw [reducedMerge831Check, Integer.Sparse.eval_mergeBy, reducedMergeEval827 B hB hF, reducedMergeEval830 B hB hF]
  rw [originalMerge831, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
