import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData33
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound31
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound32
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound33
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound34

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1056 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1056 (originalVector B) := by
  rw [reducedMerge1056Check, Integer.Sparse.eval_mergeBy, reducedTermEval1062 B hB hF, reducedTermEval1063 B hB hF]
  rw [originalMerge1056, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1057 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1057 (originalVector B) := by
  rw [reducedMerge1057Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1055 B hB hF, reducedMergeEval1056 B hB hF]
  rw [originalMerge1057, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1058 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1058 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1058 (originalVector B) := by
  rw [reducedMerge1058Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1054 B hB hF, reducedMergeEval1057 B hB hF]
  rw [originalMerge1058, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1059 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1059 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1059 (originalVector B) := by
  rw [reducedMerge1059Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1051 B hB hF, reducedMergeEval1058 B hB hF]
  rw [originalMerge1059, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1060 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1060 (originalVector B) := by
  rw [reducedMerge1060Check, Integer.Sparse.eval_mergeBy, reducedTermEval1065 B hB hF, reducedTermEval1066 B hB hF]
  rw [originalMerge1060, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1061 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1061 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1061 (originalVector B) := by
  rw [reducedMerge1061Check, Integer.Sparse.eval_mergeBy, reducedTermEval1064 B hB hF, reducedMergeEval1060 B hB hF]
  rw [originalMerge1061, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1062 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1062 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1062 (originalVector B) := by
  rw [reducedMerge1062Check, Integer.Sparse.eval_mergeBy, reducedTermEval1067 B hB hF, reducedTermEval1068 B hB hF]
  rw [originalMerge1062, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1063 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1063 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1063 (originalVector B) := by
  rw [reducedMerge1063Check, Integer.Sparse.eval_mergeBy, reducedTermEval1069 B hB hF, reducedTermEval1070 B hB hF]
  rw [originalMerge1063, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1064 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1064 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1064 (originalVector B) := by
  rw [reducedMerge1064Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1062 B hB hF, reducedMergeEval1063 B hB hF]
  rw [originalMerge1064, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1065 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1065 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1065 (originalVector B) := by
  rw [reducedMerge1065Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1061 B hB hF, reducedMergeEval1064 B hB hF]
  rw [originalMerge1065, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1066 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1066 (originalVector B) := by
  rw [reducedMerge1066Check, Integer.Sparse.eval_mergeBy, reducedTermEval1071 B hB hF, reducedTermEval1072 B hB hF]
  rw [originalMerge1066, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1067 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1067 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1067 (originalVector B) := by
  rw [reducedMerge1067Check, Integer.Sparse.eval_mergeBy, reducedTermEval1073 B hB hF, reducedTermEval1074 B hB hF]
  rw [originalMerge1067, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1068 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1068 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1068 (originalVector B) := by
  rw [reducedMerge1068Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1066 B hB hF, reducedMergeEval1067 B hB hF]
  rw [originalMerge1068, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1069 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1069 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1069 (originalVector B) := by
  rw [reducedMerge1069Check, Integer.Sparse.eval_mergeBy, reducedTermEval1075 B hB hF, reducedTermEval1076 B hB hF]
  rw [originalMerge1069, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1070 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1070 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1070 (originalVector B) := by
  rw [reducedMerge1070Check, Integer.Sparse.eval_mergeBy, reducedTermEval1077 B hB hF, reducedTermEval1078 B hB hF]
  rw [originalMerge1070, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1071 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1071 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1071 (originalVector B) := by
  rw [reducedMerge1071Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1069 B hB hF, reducedMergeEval1070 B hB hF]
  rw [originalMerge1071, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1072 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1072 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1072 (originalVector B) := by
  rw [reducedMerge1072Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1068 B hB hF, reducedMergeEval1071 B hB hF]
  rw [originalMerge1072, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1073 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1073 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1073 (originalVector B) := by
  rw [reducedMerge1073Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1065 B hB hF, reducedMergeEval1072 B hB hF]
  rw [originalMerge1073, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1074 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1074 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1074 (originalVector B) := by
  rw [reducedMerge1074Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1059 B hB hF, reducedMergeEval1073 B hB hF]
  rw [originalMerge1074, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1075 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1075 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1075 (originalVector B) := by
  rw [reducedMerge1075Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1045 B hB hF, reducedMergeEval1074 B hB hF]
  rw [originalMerge1075, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1076 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1076 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1076 (originalVector B) := by
  rw [reducedMerge1076Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1016 B hB hF, reducedMergeEval1075 B hB hF]
  rw [originalMerge1076, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1077 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1077 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1077 (originalVector B) := by
  rw [reducedMerge1077Check, Integer.Sparse.eval_mergeBy, reducedTermEval1080 B hB hF, reducedTermEval1081 B hB hF]
  rw [originalMerge1077, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1078 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1078 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1078 (originalVector B) := by
  rw [reducedMerge1078Check, Integer.Sparse.eval_mergeBy, reducedTermEval1079 B hB hF, reducedMergeEval1077 B hB hF]
  rw [originalMerge1078, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1079 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1079 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1079 (originalVector B) := by
  rw [reducedMerge1079Check, Integer.Sparse.eval_mergeBy, reducedTermEval1082 B hB hF, reducedTermEval1083 B hB hF]
  rw [originalMerge1079, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1080 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1080 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1080 (originalVector B) := by
  rw [reducedMerge1080Check, Integer.Sparse.eval_mergeBy, reducedTermEval1084 B hB hF, reducedTermEval1085 B hB hF]
  rw [originalMerge1080, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1081 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1081 (originalVector B) := by
  rw [reducedMerge1081Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1079 B hB hF, reducedMergeEval1080 B hB hF]
  rw [originalMerge1081, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1082 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1082 (originalVector B) := by
  rw [reducedMerge1082Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1078 B hB hF, reducedMergeEval1081 B hB hF]
  rw [originalMerge1082, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1083 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1083 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1083 (originalVector B) := by
  rw [reducedMerge1083Check, Integer.Sparse.eval_mergeBy, reducedTermEval1086 B hB hF, reducedTermEval1087 B hB hF]
  rw [originalMerge1083, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1084 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1084 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1084 (originalVector B) := by
  rw [reducedMerge1084Check, Integer.Sparse.eval_mergeBy, reducedTermEval1088 B hB hF, reducedTermEval1089 B hB hF]
  rw [originalMerge1084, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1085 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1085 (originalVector B) := by
  rw [reducedMerge1085Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1083 B hB hF, reducedMergeEval1084 B hB hF]
  rw [originalMerge1085, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1086 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1086 (originalVector B) := by
  rw [reducedMerge1086Check, Integer.Sparse.eval_mergeBy, reducedTermEval1090 B hB hF, reducedTermEval1091 B hB hF]
  rw [originalMerge1086, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1087 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1087 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1087 (originalVector B) := by
  rw [reducedMerge1087Check, Integer.Sparse.eval_mergeBy, reducedTermEval1092 B hB hF, reducedTermEval1093 B hB hF]
  rw [originalMerge1087, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
