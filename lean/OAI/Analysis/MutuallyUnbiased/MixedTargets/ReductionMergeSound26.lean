import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData26
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound24
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound25
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound26
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound27

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge832 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge832 (originalVector B) := by
  rw [reducedMerge832Check, Integer.Sparse.eval_mergeBy, reducedMergeEval824 B hB hF, reducedMergeEval831 B hB hF]
  rw [originalMerge832, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge833 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge833 (originalVector B) := by
  rw [reducedMerge833Check, Integer.Sparse.eval_mergeBy, reducedMergeEval818 B hB hF, reducedMergeEval832 B hB hF]
  rw [originalMerge833, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge834 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge834 (originalVector B) := by
  rw [reducedMerge834Check, Integer.Sparse.eval_mergeBy, reducedMergeEval804 B hB hF, reducedMergeEval833 B hB hF]
  rw [originalMerge834, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval835 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge835 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge835 (originalVector B) := by
  rw [reducedMerge835Check, Integer.Sparse.eval_mergeBy, reducedMergeEval775 B hB hF, reducedMergeEval834 B hB hF]
  rw [originalMerge835, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge836 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge836 (originalVector B) := by
  rw [reducedMerge836Check, Integer.Sparse.eval_mergeBy, reducedTermEval840 B hB hF, reducedTermEval841 B hB hF]
  rw [originalMerge836, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge837 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge837 (originalVector B) := by
  rw [reducedMerge837Check, Integer.Sparse.eval_mergeBy, reducedTermEval839 B hB hF, reducedMergeEval836 B hB hF]
  rw [originalMerge837, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge838 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge838 (originalVector B) := by
  rw [reducedMerge838Check, Integer.Sparse.eval_mergeBy, reducedTermEval842 B hB hF, reducedTermEval843 B hB hF]
  rw [originalMerge838, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge839 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge839 (originalVector B) := by
  rw [reducedMerge839Check, Integer.Sparse.eval_mergeBy, reducedTermEval844 B hB hF, reducedTermEval845 B hB hF]
  rw [originalMerge839, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval840 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge840 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge840 (originalVector B) := by
  rw [reducedMerge840Check, Integer.Sparse.eval_mergeBy, reducedMergeEval838 B hB hF, reducedMergeEval839 B hB hF]
  rw [originalMerge840, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge841 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge841 (originalVector B) := by
  rw [reducedMerge841Check, Integer.Sparse.eval_mergeBy, reducedMergeEval837 B hB hF, reducedMergeEval840 B hB hF]
  rw [originalMerge841, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge842 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge842 (originalVector B) := by
  rw [reducedMerge842Check, Integer.Sparse.eval_mergeBy, reducedTermEval846 B hB hF, reducedTermEval847 B hB hF]
  rw [originalMerge842, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge843 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge843 (originalVector B) := by
  rw [reducedMerge843Check, Integer.Sparse.eval_mergeBy, reducedTermEval848 B hB hF, reducedTermEval849 B hB hF]
  rw [originalMerge843, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge844 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge844 (originalVector B) := by
  rw [reducedMerge844Check, Integer.Sparse.eval_mergeBy, reducedMergeEval842 B hB hF, reducedMergeEval843 B hB hF]
  rw [originalMerge844, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge845 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge845 (originalVector B) := by
  rw [reducedMerge845Check, Integer.Sparse.eval_mergeBy, reducedTermEval850 B hB hF, reducedTermEval851 B hB hF]
  rw [originalMerge845, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge846 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge846 (originalVector B) := by
  rw [reducedMerge846Check, Integer.Sparse.eval_mergeBy, reducedTermEval852 B hB hF, reducedTermEval853 B hB hF]
  rw [originalMerge846, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval847 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge847 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge847 (originalVector B) := by
  rw [reducedMerge847Check, Integer.Sparse.eval_mergeBy, reducedMergeEval845 B hB hF, reducedMergeEval846 B hB hF]
  rw [originalMerge847, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge848 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge848 (originalVector B) := by
  rw [reducedMerge848Check, Integer.Sparse.eval_mergeBy, reducedMergeEval844 B hB hF, reducedMergeEval847 B hB hF]
  rw [originalMerge848, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge849 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge849 (originalVector B) := by
  rw [reducedMerge849Check, Integer.Sparse.eval_mergeBy, reducedMergeEval841 B hB hF, reducedMergeEval848 B hB hF]
  rw [originalMerge849, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge850 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge850 (originalVector B) := by
  rw [reducedMerge850Check, Integer.Sparse.eval_mergeBy, reducedTermEval855 B hB hF, reducedTermEval856 B hB hF]
  rw [originalMerge850, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge851 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge851 (originalVector B) := by
  rw [reducedMerge851Check, Integer.Sparse.eval_mergeBy, reducedTermEval854 B hB hF, reducedMergeEval850 B hB hF]
  rw [originalMerge851, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge852 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge852 (originalVector B) := by
  rw [reducedMerge852Check, Integer.Sparse.eval_mergeBy, reducedTermEval857 B hB hF, reducedTermEval858 B hB hF]
  rw [originalMerge852, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval853 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge853 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge853 (originalVector B) := by
  rw [reducedMerge853Check, Integer.Sparse.eval_mergeBy, reducedTermEval859 B hB hF, reducedTermEval860 B hB hF]
  rw [originalMerge853, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval854 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge854 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge854 (originalVector B) := by
  rw [reducedMerge854Check, Integer.Sparse.eval_mergeBy, reducedMergeEval852 B hB hF, reducedMergeEval853 B hB hF]
  rw [originalMerge854, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge855 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge855 (originalVector B) := by
  rw [reducedMerge855Check, Integer.Sparse.eval_mergeBy, reducedMergeEval851 B hB hF, reducedMergeEval854 B hB hF]
  rw [originalMerge855, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge856 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge856 (originalVector B) := by
  rw [reducedMerge856Check, Integer.Sparse.eval_mergeBy, reducedTermEval861 B hB hF, reducedTermEval862 B hB hF]
  rw [originalMerge856, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval857 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge857 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge857 (originalVector B) := by
  rw [reducedMerge857Check, Integer.Sparse.eval_mergeBy, reducedTermEval863 B hB hF, reducedTermEval864 B hB hF]
  rw [originalMerge857, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval858 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge858 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge858 (originalVector B) := by
  rw [reducedMerge858Check, Integer.Sparse.eval_mergeBy, reducedMergeEval856 B hB hF, reducedMergeEval857 B hB hF]
  rw [originalMerge858, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge859 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge859 (originalVector B) := by
  rw [reducedMerge859Check, Integer.Sparse.eval_mergeBy, reducedTermEval865 B hB hF, reducedTermEval866 B hB hF]
  rw [originalMerge859, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge860 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge860 (originalVector B) := by
  rw [reducedMerge860Check, Integer.Sparse.eval_mergeBy, reducedTermEval867 B hB hF, reducedTermEval868 B hB hF]
  rw [originalMerge860, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge861 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge861 (originalVector B) := by
  rw [reducedMerge861Check, Integer.Sparse.eval_mergeBy, reducedMergeEval859 B hB hF, reducedMergeEval860 B hB hF]
  rw [originalMerge861, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval862 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge862 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge862 (originalVector B) := by
  rw [reducedMerge862Check, Integer.Sparse.eval_mergeBy, reducedMergeEval858 B hB hF, reducedMergeEval861 B hB hF]
  rw [originalMerge862, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval863 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge863 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge863 (originalVector B) := by
  rw [reducedMerge863Check, Integer.Sparse.eval_mergeBy, reducedMergeEval855 B hB hF, reducedMergeEval862 B hB hF]
  rw [originalMerge863, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
