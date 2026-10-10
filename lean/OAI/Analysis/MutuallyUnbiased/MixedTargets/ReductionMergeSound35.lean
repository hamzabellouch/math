import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData35
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound34
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound35
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound36

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1120 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1120 (originalVector B) := by
  rw [reducedMerge1120Check, Integer.Sparse.eval_mergeBy, reducedTermEval1125 B hB hF, reducedTermEval1126 B hB hF]
  rw [originalMerge1120, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1121 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1121 (originalVector B) := by
  rw [reducedMerge1121Check, Integer.Sparse.eval_mergeBy, reducedTermEval1124 B hB hF, reducedMergeEval1120 B hB hF]
  rw [originalMerge1121, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1122 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1122 (originalVector B) := by
  rw [reducedMerge1122Check, Integer.Sparse.eval_mergeBy, reducedTermEval1127 B hB hF, reducedTermEval1128 B hB hF]
  rw [originalMerge1122, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1123 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1123 (originalVector B) := by
  rw [reducedMerge1123Check, Integer.Sparse.eval_mergeBy, reducedTermEval1129 B hB hF, reducedTermEval1130 B hB hF]
  rw [originalMerge1123, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1124 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1124 (originalVector B) := by
  rw [reducedMerge1124Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1122 B hB hF, reducedMergeEval1123 B hB hF]
  rw [originalMerge1124, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1125 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1125 (originalVector B) := by
  rw [reducedMerge1125Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1121 B hB hF, reducedMergeEval1124 B hB hF]
  rw [originalMerge1125, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1126 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1126 (originalVector B) := by
  rw [reducedMerge1126Check, Integer.Sparse.eval_mergeBy, reducedTermEval1131 B hB hF, reducedTermEval1132 B hB hF]
  rw [originalMerge1126, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1127 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1127 (originalVector B) := by
  rw [reducedMerge1127Check, Integer.Sparse.eval_mergeBy, reducedTermEval1133 B hB hF, reducedTermEval1134 B hB hF]
  rw [originalMerge1127, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1128 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1128 (originalVector B) := by
  rw [reducedMerge1128Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1126 B hB hF, reducedMergeEval1127 B hB hF]
  rw [originalMerge1128, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1129 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1129 (originalVector B) := by
  rw [reducedMerge1129Check, Integer.Sparse.eval_mergeBy, reducedTermEval1135 B hB hF, reducedTermEval1136 B hB hF]
  rw [originalMerge1129, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1130 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1130 (originalVector B) := by
  rw [reducedMerge1130Check, Integer.Sparse.eval_mergeBy, reducedTermEval1137 B hB hF, reducedTermEval1138 B hB hF]
  rw [originalMerge1130, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1131 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1131 (originalVector B) := by
  rw [reducedMerge1131Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1129 B hB hF, reducedMergeEval1130 B hB hF]
  rw [originalMerge1131, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1132 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1132 (originalVector B) := by
  rw [reducedMerge1132Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1128 B hB hF, reducedMergeEval1131 B hB hF]
  rw [originalMerge1132, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1133 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1133 (originalVector B) := by
  rw [reducedMerge1133Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1125 B hB hF, reducedMergeEval1132 B hB hF]
  rw [originalMerge1133, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1134 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1134 (originalVector B) := by
  rw [reducedMerge1134Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1119 B hB hF, reducedMergeEval1133 B hB hF]
  rw [originalMerge1134, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1135 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1135 (originalVector B) := by
  rw [reducedMerge1135Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1105 B hB hF, reducedMergeEval1134 B hB hF]
  rw [originalMerge1135, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1136 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1136 (originalVector B) := by
  rw [reducedMerge1136Check, Integer.Sparse.eval_mergeBy, reducedTermEval1140 B hB hF, reducedTermEval1141 B hB hF]
  rw [originalMerge1136, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1137 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1137 (originalVector B) := by
  rw [reducedMerge1137Check, Integer.Sparse.eval_mergeBy, reducedTermEval1139 B hB hF, reducedMergeEval1136 B hB hF]
  rw [originalMerge1137, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1138 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1138 (originalVector B) := by
  rw [reducedMerge1138Check, Integer.Sparse.eval_mergeBy, reducedTermEval1142 B hB hF, reducedTermEval1143 B hB hF]
  rw [originalMerge1138, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1139 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1139 (originalVector B) := by
  rw [reducedMerge1139Check, Integer.Sparse.eval_mergeBy, reducedTermEval1144 B hB hF, reducedTermEval1145 B hB hF]
  rw [originalMerge1139, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1140 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1140 (originalVector B) := by
  rw [reducedMerge1140Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1138 B hB hF, reducedMergeEval1139 B hB hF]
  rw [originalMerge1140, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1141 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1141 (originalVector B) := by
  rw [reducedMerge1141Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1137 B hB hF, reducedMergeEval1140 B hB hF]
  rw [originalMerge1141, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1142 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1142 (originalVector B) := by
  rw [reducedMerge1142Check, Integer.Sparse.eval_mergeBy, reducedTermEval1146 B hB hF, reducedTermEval1147 B hB hF]
  rw [originalMerge1142, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1143 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1143 (originalVector B) := by
  rw [reducedMerge1143Check, Integer.Sparse.eval_mergeBy, reducedTermEval1148 B hB hF, reducedTermEval1149 B hB hF]
  rw [originalMerge1143, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1144 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1144 (originalVector B) := by
  rw [reducedMerge1144Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1142 B hB hF, reducedMergeEval1143 B hB hF]
  rw [originalMerge1144, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1145 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1145 (originalVector B) := by
  rw [reducedMerge1145Check, Integer.Sparse.eval_mergeBy, reducedTermEval1150 B hB hF, reducedTermEval1151 B hB hF]
  rw [originalMerge1145, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1146 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1146 (originalVector B) := by
  rw [reducedMerge1146Check, Integer.Sparse.eval_mergeBy, reducedTermEval1152 B hB hF, reducedTermEval1153 B hB hF]
  rw [originalMerge1146, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1147 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1147 (originalVector B) := by
  rw [reducedMerge1147Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1145 B hB hF, reducedMergeEval1146 B hB hF]
  rw [originalMerge1147, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1148 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1148 (originalVector B) := by
  rw [reducedMerge1148Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1144 B hB hF, reducedMergeEval1147 B hB hF]
  rw [originalMerge1148, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1149 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1149 (originalVector B) := by
  rw [reducedMerge1149Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1141 B hB hF, reducedMergeEval1148 B hB hF]
  rw [originalMerge1149, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1150 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1150 (originalVector B) := by
  rw [reducedMerge1150Check, Integer.Sparse.eval_mergeBy, reducedTermEval1155 B hB hF, reducedTermEval1156 B hB hF]
  rw [originalMerge1150, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1151 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1151 (originalVector B) := by
  rw [reducedMerge1151Check, Integer.Sparse.eval_mergeBy, reducedTermEval1154 B hB hF, reducedMergeEval1150 B hB hF]
  rw [originalMerge1151, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
