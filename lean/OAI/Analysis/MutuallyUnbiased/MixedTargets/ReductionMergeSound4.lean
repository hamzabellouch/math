import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData4
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound3
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound4
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound5

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge128 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge128 (originalVector B) := by
  rw [reducedMerge128Check, Integer.Sparse.eval_mergeBy, reducedTermEval132 B hB hF, reducedTermEval133 B hB hF]
  rw [originalMerge128, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge129 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge129 (originalVector B) := by
  rw [reducedMerge129Check, Integer.Sparse.eval_mergeBy, reducedMergeEval127 B hB hF, reducedMergeEval128 B hB hF]
  rw [originalMerge129, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge130 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge130 (originalVector B) := by
  rw [reducedMerge130Check, Integer.Sparse.eval_mergeBy, reducedMergeEval126 B hB hF, reducedMergeEval129 B hB hF]
  rw [originalMerge130, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge131 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge131 (originalVector B) := by
  rw [reducedMerge131Check, Integer.Sparse.eval_mergeBy, reducedMergeEval123 B hB hF, reducedMergeEval130 B hB hF]
  rw [originalMerge131, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge132 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge132 (originalVector B) := by
  rw [reducedMerge132Check, Integer.Sparse.eval_mergeBy, reducedTermEval135 B hB hF, reducedTermEval136 B hB hF]
  rw [originalMerge132, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge133 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge133 (originalVector B) := by
  rw [reducedMerge133Check, Integer.Sparse.eval_mergeBy, reducedTermEval134 B hB hF, reducedMergeEval132 B hB hF]
  rw [originalMerge133, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge134 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge134 (originalVector B) := by
  rw [reducedMerge134Check, Integer.Sparse.eval_mergeBy, reducedTermEval137 B hB hF, reducedTermEval138 B hB hF]
  rw [originalMerge134, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge135 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge135 (originalVector B) := by
  rw [reducedMerge135Check, Integer.Sparse.eval_mergeBy, reducedTermEval139 B hB hF, reducedTermEval140 B hB hF]
  rw [originalMerge135, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge136 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge136 (originalVector B) := by
  rw [reducedMerge136Check, Integer.Sparse.eval_mergeBy, reducedMergeEval134 B hB hF, reducedMergeEval135 B hB hF]
  rw [originalMerge136, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge137 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge137 (originalVector B) := by
  rw [reducedMerge137Check, Integer.Sparse.eval_mergeBy, reducedMergeEval133 B hB hF, reducedMergeEval136 B hB hF]
  rw [originalMerge137, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge138 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge138 (originalVector B) := by
  rw [reducedMerge138Check, Integer.Sparse.eval_mergeBy, reducedTermEval141 B hB hF, reducedTermEval142 B hB hF]
  rw [originalMerge138, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge139 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge139 (originalVector B) := by
  rw [reducedMerge139Check, Integer.Sparse.eval_mergeBy, reducedTermEval143 B hB hF, reducedTermEval144 B hB hF]
  rw [originalMerge139, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge140 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge140 (originalVector B) := by
  rw [reducedMerge140Check, Integer.Sparse.eval_mergeBy, reducedMergeEval138 B hB hF, reducedMergeEval139 B hB hF]
  rw [originalMerge140, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge141 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge141 (originalVector B) := by
  rw [reducedMerge141Check, Integer.Sparse.eval_mergeBy, reducedTermEval145 B hB hF, reducedTermEval146 B hB hF]
  rw [originalMerge141, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge142 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge142 (originalVector B) := by
  rw [reducedMerge142Check, Integer.Sparse.eval_mergeBy, reducedTermEval147 B hB hF, reducedTermEval148 B hB hF]
  rw [originalMerge142, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge143 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge143 (originalVector B) := by
  rw [reducedMerge143Check, Integer.Sparse.eval_mergeBy, reducedMergeEval141 B hB hF, reducedMergeEval142 B hB hF]
  rw [originalMerge143, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge144 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge144 (originalVector B) := by
  rw [reducedMerge144Check, Integer.Sparse.eval_mergeBy, reducedMergeEval140 B hB hF, reducedMergeEval143 B hB hF]
  rw [originalMerge144, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge145 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge145 (originalVector B) := by
  rw [reducedMerge145Check, Integer.Sparse.eval_mergeBy, reducedMergeEval137 B hB hF, reducedMergeEval144 B hB hF]
  rw [originalMerge145, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge146 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge146 (originalVector B) := by
  rw [reducedMerge146Check, Integer.Sparse.eval_mergeBy, reducedMergeEval131 B hB hF, reducedMergeEval145 B hB hF]
  rw [originalMerge146, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge147 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge147 (originalVector B) := by
  rw [reducedMerge147Check, Integer.Sparse.eval_mergeBy, reducedTermEval150 B hB hF, reducedTermEval151 B hB hF]
  rw [originalMerge147, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge148 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge148 (originalVector B) := by
  rw [reducedMerge148Check, Integer.Sparse.eval_mergeBy, reducedTermEval149 B hB hF, reducedMergeEval147 B hB hF]
  rw [originalMerge148, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge149 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge149 (originalVector B) := by
  rw [reducedMerge149Check, Integer.Sparse.eval_mergeBy, reducedTermEval152 B hB hF, reducedTermEval153 B hB hF]
  rw [originalMerge149, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge150 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge150 (originalVector B) := by
  rw [reducedMerge150Check, Integer.Sparse.eval_mergeBy, reducedTermEval154 B hB hF, reducedTermEval155 B hB hF]
  rw [originalMerge150, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge151 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge151 (originalVector B) := by
  rw [reducedMerge151Check, Integer.Sparse.eval_mergeBy, reducedMergeEval149 B hB hF, reducedMergeEval150 B hB hF]
  rw [originalMerge151, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge152 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge152 (originalVector B) := by
  rw [reducedMerge152Check, Integer.Sparse.eval_mergeBy, reducedMergeEval148 B hB hF, reducedMergeEval151 B hB hF]
  rw [originalMerge152, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge153 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge153 (originalVector B) := by
  rw [reducedMerge153Check, Integer.Sparse.eval_mergeBy, reducedTermEval156 B hB hF, reducedTermEval157 B hB hF]
  rw [originalMerge153, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge154 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge154 (originalVector B) := by
  rw [reducedMerge154Check, Integer.Sparse.eval_mergeBy, reducedTermEval158 B hB hF, reducedTermEval159 B hB hF]
  rw [originalMerge154, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge155 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge155 (originalVector B) := by
  rw [reducedMerge155Check, Integer.Sparse.eval_mergeBy, reducedMergeEval153 B hB hF, reducedMergeEval154 B hB hF]
  rw [originalMerge155, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge156 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge156 (originalVector B) := by
  rw [reducedMerge156Check, Integer.Sparse.eval_mergeBy, reducedTermEval160 B hB hF, reducedTermEval161 B hB hF]
  rw [originalMerge156, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge157 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge157 (originalVector B) := by
  rw [reducedMerge157Check, Integer.Sparse.eval_mergeBy, reducedTermEval162 B hB hF, reducedTermEval163 B hB hF]
  rw [originalMerge157, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge158 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge158 (originalVector B) := by
  rw [reducedMerge158Check, Integer.Sparse.eval_mergeBy, reducedMergeEval156 B hB hF, reducedMergeEval157 B hB hF]
  rw [originalMerge158, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge159 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge159 (originalVector B) := by
  rw [reducedMerge159Check, Integer.Sparse.eval_mergeBy, reducedMergeEval155 B hB hF, reducedMergeEval158 B hB hF]
  rw [originalMerge159, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
