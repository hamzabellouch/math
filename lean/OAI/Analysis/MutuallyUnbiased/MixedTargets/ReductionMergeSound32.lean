import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData32
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound31
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound32
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound33

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1024 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1024 (originalVector B) := by
  rw [reducedMerge1024Check, Integer.Sparse.eval_mergeBy, reducedTermEval1028 B hB hF, reducedTermEval1029 B hB hF]
  rw [originalMerge1024, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1025 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1025 (originalVector B) := by
  rw [reducedMerge1025Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1023 B hB hF, reducedMergeEval1024 B hB hF]
  rw [originalMerge1025, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1026 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1026 (originalVector B) := by
  rw [reducedMerge1026Check, Integer.Sparse.eval_mergeBy, reducedTermEval1030 B hB hF, reducedTermEval1031 B hB hF]
  rw [originalMerge1026, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1027 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1027 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1027 (originalVector B) := by
  rw [reducedMerge1027Check, Integer.Sparse.eval_mergeBy, reducedTermEval1032 B hB hF, reducedTermEval1033 B hB hF]
  rw [originalMerge1027, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1028 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1028 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1028 (originalVector B) := by
  rw [reducedMerge1028Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1026 B hB hF, reducedMergeEval1027 B hB hF]
  rw [originalMerge1028, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1029 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1029 (originalVector B) := by
  rw [reducedMerge1029Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1025 B hB hF, reducedMergeEval1028 B hB hF]
  rw [originalMerge1029, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1030 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1030 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1030 (originalVector B) := by
  rw [reducedMerge1030Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1022 B hB hF, reducedMergeEval1029 B hB hF]
  rw [originalMerge1030, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1031 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1031 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1031 (originalVector B) := by
  rw [reducedMerge1031Check, Integer.Sparse.eval_mergeBy, reducedTermEval1035 B hB hF, reducedTermEval1036 B hB hF]
  rw [originalMerge1031, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1032 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1032 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1032 (originalVector B) := by
  rw [reducedMerge1032Check, Integer.Sparse.eval_mergeBy, reducedTermEval1034 B hB hF, reducedMergeEval1031 B hB hF]
  rw [originalMerge1032, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1033 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1033 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1033 (originalVector B) := by
  rw [reducedMerge1033Check, Integer.Sparse.eval_mergeBy, reducedTermEval1037 B hB hF, reducedTermEval1038 B hB hF]
  rw [originalMerge1033, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1034 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1034 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1034 (originalVector B) := by
  rw [reducedMerge1034Check, Integer.Sparse.eval_mergeBy, reducedTermEval1039 B hB hF, reducedTermEval1040 B hB hF]
  rw [originalMerge1034, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1035 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1035 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1035 (originalVector B) := by
  rw [reducedMerge1035Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1033 B hB hF, reducedMergeEval1034 B hB hF]
  rw [originalMerge1035, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1036 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1036 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1036 (originalVector B) := by
  rw [reducedMerge1036Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1032 B hB hF, reducedMergeEval1035 B hB hF]
  rw [originalMerge1036, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1037 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1037 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1037 (originalVector B) := by
  rw [reducedMerge1037Check, Integer.Sparse.eval_mergeBy, reducedTermEval1041 B hB hF, reducedTermEval1042 B hB hF]
  rw [originalMerge1037, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1038 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1038 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1038 (originalVector B) := by
  rw [reducedMerge1038Check, Integer.Sparse.eval_mergeBy, reducedTermEval1043 B hB hF, reducedTermEval1044 B hB hF]
  rw [originalMerge1038, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1039 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1039 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1039 (originalVector B) := by
  rw [reducedMerge1039Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1037 B hB hF, reducedMergeEval1038 B hB hF]
  rw [originalMerge1039, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1040 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1040 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1040 (originalVector B) := by
  rw [reducedMerge1040Check, Integer.Sparse.eval_mergeBy, reducedTermEval1045 B hB hF, reducedTermEval1046 B hB hF]
  rw [originalMerge1040, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1041 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1041 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1041 (originalVector B) := by
  rw [reducedMerge1041Check, Integer.Sparse.eval_mergeBy, reducedTermEval1047 B hB hF, reducedTermEval1048 B hB hF]
  rw [originalMerge1041, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1042 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1042 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1042 (originalVector B) := by
  rw [reducedMerge1042Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1040 B hB hF, reducedMergeEval1041 B hB hF]
  rw [originalMerge1042, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1043 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1043 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1043 (originalVector B) := by
  rw [reducedMerge1043Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1039 B hB hF, reducedMergeEval1042 B hB hF]
  rw [originalMerge1043, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1044 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1044 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1044 (originalVector B) := by
  rw [reducedMerge1044Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1036 B hB hF, reducedMergeEval1043 B hB hF]
  rw [originalMerge1044, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1045 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1045 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1045 (originalVector B) := by
  rw [reducedMerge1045Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1030 B hB hF, reducedMergeEval1044 B hB hF]
  rw [originalMerge1045, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1046 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1046 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1046 (originalVector B) := by
  rw [reducedMerge1046Check, Integer.Sparse.eval_mergeBy, reducedTermEval1050 B hB hF, reducedTermEval1051 B hB hF]
  rw [originalMerge1046, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1047 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1047 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1047 (originalVector B) := by
  rw [reducedMerge1047Check, Integer.Sparse.eval_mergeBy, reducedTermEval1049 B hB hF, reducedMergeEval1046 B hB hF]
  rw [originalMerge1047, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1048 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1048 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1048 (originalVector B) := by
  rw [reducedMerge1048Check, Integer.Sparse.eval_mergeBy, reducedTermEval1052 B hB hF, reducedTermEval1053 B hB hF]
  rw [originalMerge1048, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1049 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1049 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1049 (originalVector B) := by
  rw [reducedMerge1049Check, Integer.Sparse.eval_mergeBy, reducedTermEval1054 B hB hF, reducedTermEval1055 B hB hF]
  rw [originalMerge1049, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1050 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1050 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1050 (originalVector B) := by
  rw [reducedMerge1050Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1048 B hB hF, reducedMergeEval1049 B hB hF]
  rw [originalMerge1050, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1051 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1051 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1051 (originalVector B) := by
  rw [reducedMerge1051Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1047 B hB hF, reducedMergeEval1050 B hB hF]
  rw [originalMerge1051, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1052 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1052 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1052 (originalVector B) := by
  rw [reducedMerge1052Check, Integer.Sparse.eval_mergeBy, reducedTermEval1056 B hB hF, reducedTermEval1057 B hB hF]
  rw [originalMerge1052, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1053 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1053 (originalVector B) := by
  rw [reducedMerge1053Check, Integer.Sparse.eval_mergeBy, reducedTermEval1058 B hB hF, reducedTermEval1059 B hB hF]
  rw [originalMerge1053, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1054 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1054 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1054 (originalVector B) := by
  rw [reducedMerge1054Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1052 B hB hF, reducedMergeEval1053 B hB hF]
  rw [originalMerge1054, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1055 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1055 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1055 (originalVector B) := by
  rw [reducedMerge1055Check, Integer.Sparse.eval_mergeBy, reducedTermEval1060 B hB hF, reducedTermEval1061 B hB hF]
  rw [originalMerge1055, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
