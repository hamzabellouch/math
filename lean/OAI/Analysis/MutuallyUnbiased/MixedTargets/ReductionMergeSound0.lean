import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData0
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound0
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound1

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval0 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge0 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge0 (originalVector B) := by
  rw [reducedMerge0Check, Integer.Sparse.eval_mergeBy, reducedTermEval1 B hB hF, reducedTermEval2 B hB hF]
  rw [originalMerge0, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1 (originalVector B) := by
  rw [reducedMerge1Check, Integer.Sparse.eval_mergeBy, reducedTermEval0 B hB hF, reducedMergeEval0 B hB hF]
  rw [originalMerge1, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval2 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge2 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge2 (originalVector B) := by
  rw [reducedMerge2Check, Integer.Sparse.eval_mergeBy, reducedTermEval3 B hB hF, reducedTermEval4 B hB hF]
  rw [originalMerge2, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval3 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge3 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge3 (originalVector B) := by
  rw [reducedMerge3Check, Integer.Sparse.eval_mergeBy, reducedTermEval5 B hB hF, reducedTermEval6 B hB hF]
  rw [originalMerge3, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval4 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge4 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge4 (originalVector B) := by
  rw [reducedMerge4Check, Integer.Sparse.eval_mergeBy, reducedMergeEval2 B hB hF, reducedMergeEval3 B hB hF]
  rw [originalMerge4, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval5 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge5 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge5 (originalVector B) := by
  rw [reducedMerge5Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1 B hB hF, reducedMergeEval4 B hB hF]
  rw [originalMerge5, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval6 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge6 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge6 (originalVector B) := by
  rw [reducedMerge6Check, Integer.Sparse.eval_mergeBy, reducedTermEval8 B hB hF, reducedTermEval9 B hB hF]
  rw [originalMerge6, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval7 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge7 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge7 (originalVector B) := by
  rw [reducedMerge7Check, Integer.Sparse.eval_mergeBy, reducedTermEval7 B hB hF, reducedMergeEval6 B hB hF]
  rw [originalMerge7, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval8 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge8 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge8 (originalVector B) := by
  rw [reducedMerge8Check, Integer.Sparse.eval_mergeBy, reducedTermEval10 B hB hF, reducedTermEval11 B hB hF]
  rw [originalMerge8, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval9 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge9 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge9 (originalVector B) := by
  rw [reducedMerge9Check, Integer.Sparse.eval_mergeBy, reducedTermEval12 B hB hF, reducedTermEval13 B hB hF]
  rw [originalMerge9, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval10 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge10 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge10 (originalVector B) := by
  rw [reducedMerge10Check, Integer.Sparse.eval_mergeBy, reducedMergeEval8 B hB hF, reducedMergeEval9 B hB hF]
  rw [originalMerge10, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval11 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge11 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge11 (originalVector B) := by
  rw [reducedMerge11Check, Integer.Sparse.eval_mergeBy, reducedMergeEval7 B hB hF, reducedMergeEval10 B hB hF]
  rw [originalMerge11, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval12 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge12 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge12 (originalVector B) := by
  rw [reducedMerge12Check, Integer.Sparse.eval_mergeBy, reducedMergeEval5 B hB hF, reducedMergeEval11 B hB hF]
  rw [originalMerge12, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval13 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge13 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge13 (originalVector B) := by
  rw [reducedMerge13Check, Integer.Sparse.eval_mergeBy, reducedTermEval15 B hB hF, reducedTermEval16 B hB hF]
  rw [originalMerge13, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval14 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge14 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge14 (originalVector B) := by
  rw [reducedMerge14Check, Integer.Sparse.eval_mergeBy, reducedTermEval14 B hB hF, reducedMergeEval13 B hB hF]
  rw [originalMerge14, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval15 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge15 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge15 (originalVector B) := by
  rw [reducedMerge15Check, Integer.Sparse.eval_mergeBy, reducedTermEval17 B hB hF, reducedTermEval18 B hB hF]
  rw [originalMerge15, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval16 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge16 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge16 (originalVector B) := by
  rw [reducedMerge16Check, Integer.Sparse.eval_mergeBy, reducedTermEval19 B hB hF, reducedTermEval20 B hB hF]
  rw [originalMerge16, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval17 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge17 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge17 (originalVector B) := by
  rw [reducedMerge17Check, Integer.Sparse.eval_mergeBy, reducedMergeEval15 B hB hF, reducedMergeEval16 B hB hF]
  rw [originalMerge17, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval18 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge18 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge18 (originalVector B) := by
  rw [reducedMerge18Check, Integer.Sparse.eval_mergeBy, reducedMergeEval14 B hB hF, reducedMergeEval17 B hB hF]
  rw [originalMerge18, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval19 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge19 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge19 (originalVector B) := by
  rw [reducedMerge19Check, Integer.Sparse.eval_mergeBy, reducedTermEval21 B hB hF, reducedTermEval22 B hB hF]
  rw [originalMerge19, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval20 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge20 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge20 (originalVector B) := by
  rw [reducedMerge20Check, Integer.Sparse.eval_mergeBy, reducedTermEval23 B hB hF, reducedTermEval24 B hB hF]
  rw [originalMerge20, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval21 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge21 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge21 (originalVector B) := by
  rw [reducedMerge21Check, Integer.Sparse.eval_mergeBy, reducedMergeEval19 B hB hF, reducedMergeEval20 B hB hF]
  rw [originalMerge21, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval22 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge22 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge22 (originalVector B) := by
  rw [reducedMerge22Check, Integer.Sparse.eval_mergeBy, reducedTermEval25 B hB hF, reducedTermEval26 B hB hF]
  rw [originalMerge22, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval23 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge23 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge23 (originalVector B) := by
  rw [reducedMerge23Check, Integer.Sparse.eval_mergeBy, reducedTermEval27 B hB hF, reducedTermEval28 B hB hF]
  rw [originalMerge23, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval24 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge24 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge24 (originalVector B) := by
  rw [reducedMerge24Check, Integer.Sparse.eval_mergeBy, reducedMergeEval22 B hB hF, reducedMergeEval23 B hB hF]
  rw [originalMerge24, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval25 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge25 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge25 (originalVector B) := by
  rw [reducedMerge25Check, Integer.Sparse.eval_mergeBy, reducedMergeEval21 B hB hF, reducedMergeEval24 B hB hF]
  rw [originalMerge25, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval26 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge26 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge26 (originalVector B) := by
  rw [reducedMerge26Check, Integer.Sparse.eval_mergeBy, reducedMergeEval18 B hB hF, reducedMergeEval25 B hB hF]
  rw [originalMerge26, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval27 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge27 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge27 (originalVector B) := by
  rw [reducedMerge27Check, Integer.Sparse.eval_mergeBy, reducedMergeEval12 B hB hF, reducedMergeEval26 B hB hF]
  rw [originalMerge27, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval28 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge28 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge28 (originalVector B) := by
  rw [reducedMerge28Check, Integer.Sparse.eval_mergeBy, reducedTermEval30 B hB hF, reducedTermEval31 B hB hF]
  rw [originalMerge28, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval29 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge29 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge29 (originalVector B) := by
  rw [reducedMerge29Check, Integer.Sparse.eval_mergeBy, reducedTermEval29 B hB hF, reducedMergeEval28 B hB hF]
  rw [originalMerge29, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval30 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge30 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge30 (originalVector B) := by
  rw [reducedMerge30Check, Integer.Sparse.eval_mergeBy, reducedTermEval32 B hB hF, reducedTermEval33 B hB hF]
  rw [originalMerge30, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval31 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge31 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge31 (originalVector B) := by
  rw [reducedMerge31Check, Integer.Sparse.eval_mergeBy, reducedTermEval34 B hB hF, reducedTermEval35 B hB hF]
  rw [originalMerge31, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
