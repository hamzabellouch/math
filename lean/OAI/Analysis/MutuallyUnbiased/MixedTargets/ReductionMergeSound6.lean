import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData6
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound5
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound6
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound7

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval192 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge192 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge192 (originalVector B) := by
  rw [reducedMerge192Check, Integer.Sparse.eval_mergeBy, reducedTermEval194 B hB hF, reducedMergeEval191 B hB hF]
  rw [originalMerge192, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval193 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge193 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge193 (originalVector B) := by
  rw [reducedMerge193Check, Integer.Sparse.eval_mergeBy, reducedTermEval197 B hB hF, reducedTermEval198 B hB hF]
  rw [originalMerge193, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval194 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge194 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge194 (originalVector B) := by
  rw [reducedMerge194Check, Integer.Sparse.eval_mergeBy, reducedTermEval199 B hB hF, reducedTermEval200 B hB hF]
  rw [originalMerge194, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval195 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge195 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge195 (originalVector B) := by
  rw [reducedMerge195Check, Integer.Sparse.eval_mergeBy, reducedMergeEval193 B hB hF, reducedMergeEval194 B hB hF]
  rw [originalMerge195, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval196 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge196 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge196 (originalVector B) := by
  rw [reducedMerge196Check, Integer.Sparse.eval_mergeBy, reducedMergeEval192 B hB hF, reducedMergeEval195 B hB hF]
  rw [originalMerge196, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval197 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge197 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge197 (originalVector B) := by
  rw [reducedMerge197Check, Integer.Sparse.eval_mergeBy, reducedTermEval201 B hB hF, reducedTermEval202 B hB hF]
  rw [originalMerge197, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval198 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge198 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge198 (originalVector B) := by
  rw [reducedMerge198Check, Integer.Sparse.eval_mergeBy, reducedTermEval203 B hB hF, reducedTermEval204 B hB hF]
  rw [originalMerge198, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval199 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge199 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge199 (originalVector B) := by
  rw [reducedMerge199Check, Integer.Sparse.eval_mergeBy, reducedMergeEval197 B hB hF, reducedMergeEval198 B hB hF]
  rw [originalMerge199, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval200 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge200 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge200 (originalVector B) := by
  rw [reducedMerge200Check, Integer.Sparse.eval_mergeBy, reducedTermEval205 B hB hF, reducedTermEval206 B hB hF]
  rw [originalMerge200, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval201 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge201 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge201 (originalVector B) := by
  rw [reducedMerge201Check, Integer.Sparse.eval_mergeBy, reducedTermEval207 B hB hF, reducedTermEval208 B hB hF]
  rw [originalMerge201, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval202 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge202 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge202 (originalVector B) := by
  rw [reducedMerge202Check, Integer.Sparse.eval_mergeBy, reducedMergeEval200 B hB hF, reducedMergeEval201 B hB hF]
  rw [originalMerge202, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval203 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge203 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge203 (originalVector B) := by
  rw [reducedMerge203Check, Integer.Sparse.eval_mergeBy, reducedMergeEval199 B hB hF, reducedMergeEval202 B hB hF]
  rw [originalMerge203, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge204 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge204 (originalVector B) := by
  rw [reducedMerge204Check, Integer.Sparse.eval_mergeBy, reducedMergeEval196 B hB hF, reducedMergeEval203 B hB hF]
  rw [originalMerge204, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge205 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge205 (originalVector B) := by
  rw [reducedMerge205Check, Integer.Sparse.eval_mergeBy, reducedMergeEval190 B hB hF, reducedMergeEval204 B hB hF]
  rw [originalMerge205, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval206 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge206 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge206 (originalVector B) := by
  rw [reducedMerge206Check, Integer.Sparse.eval_mergeBy, reducedTermEval210 B hB hF, reducedTermEval211 B hB hF]
  rw [originalMerge206, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval207 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge207 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge207 (originalVector B) := by
  rw [reducedMerge207Check, Integer.Sparse.eval_mergeBy, reducedTermEval209 B hB hF, reducedMergeEval206 B hB hF]
  rw [originalMerge207, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval208 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge208 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge208 (originalVector B) := by
  rw [reducedMerge208Check, Integer.Sparse.eval_mergeBy, reducedTermEval212 B hB hF, reducedTermEval213 B hB hF]
  rw [originalMerge208, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval209 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge209 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge209 (originalVector B) := by
  rw [reducedMerge209Check, Integer.Sparse.eval_mergeBy, reducedTermEval214 B hB hF, reducedTermEval215 B hB hF]
  rw [originalMerge209, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval210 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge210 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge210 (originalVector B) := by
  rw [reducedMerge210Check, Integer.Sparse.eval_mergeBy, reducedMergeEval208 B hB hF, reducedMergeEval209 B hB hF]
  rw [originalMerge210, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval211 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge211 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge211 (originalVector B) := by
  rw [reducedMerge211Check, Integer.Sparse.eval_mergeBy, reducedMergeEval207 B hB hF, reducedMergeEval210 B hB hF]
  rw [originalMerge211, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval212 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge212 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge212 (originalVector B) := by
  rw [reducedMerge212Check, Integer.Sparse.eval_mergeBy, reducedTermEval216 B hB hF, reducedTermEval217 B hB hF]
  rw [originalMerge212, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval213 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge213 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge213 (originalVector B) := by
  rw [reducedMerge213Check, Integer.Sparse.eval_mergeBy, reducedTermEval218 B hB hF, reducedTermEval219 B hB hF]
  rw [originalMerge213, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval214 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge214 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge214 (originalVector B) := by
  rw [reducedMerge214Check, Integer.Sparse.eval_mergeBy, reducedMergeEval212 B hB hF, reducedMergeEval213 B hB hF]
  rw [originalMerge214, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval215 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge215 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge215 (originalVector B) := by
  rw [reducedMerge215Check, Integer.Sparse.eval_mergeBy, reducedTermEval220 B hB hF, reducedTermEval221 B hB hF]
  rw [originalMerge215, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval216 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge216 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge216 (originalVector B) := by
  rw [reducedMerge216Check, Integer.Sparse.eval_mergeBy, reducedTermEval222 B hB hF, reducedTermEval223 B hB hF]
  rw [originalMerge216, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval217 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge217 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge217 (originalVector B) := by
  rw [reducedMerge217Check, Integer.Sparse.eval_mergeBy, reducedMergeEval215 B hB hF, reducedMergeEval216 B hB hF]
  rw [originalMerge217, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval218 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge218 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge218 (originalVector B) := by
  rw [reducedMerge218Check, Integer.Sparse.eval_mergeBy, reducedMergeEval214 B hB hF, reducedMergeEval217 B hB hF]
  rw [originalMerge218, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval219 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge219 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge219 (originalVector B) := by
  rw [reducedMerge219Check, Integer.Sparse.eval_mergeBy, reducedMergeEval211 B hB hF, reducedMergeEval218 B hB hF]
  rw [originalMerge219, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval220 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge220 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge220 (originalVector B) := by
  rw [reducedMerge220Check, Integer.Sparse.eval_mergeBy, reducedTermEval225 B hB hF, reducedTermEval226 B hB hF]
  rw [originalMerge220, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval221 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge221 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge221 (originalVector B) := by
  rw [reducedMerge221Check, Integer.Sparse.eval_mergeBy, reducedTermEval224 B hB hF, reducedMergeEval220 B hB hF]
  rw [originalMerge221, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval222 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge222 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge222 (originalVector B) := by
  rw [reducedMerge222Check, Integer.Sparse.eval_mergeBy, reducedTermEval227 B hB hF, reducedTermEval228 B hB hF]
  rw [originalMerge222, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval223 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge223 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge223 (originalVector B) := by
  rw [reducedMerge223Check, Integer.Sparse.eval_mergeBy, reducedTermEval229 B hB hF, reducedTermEval230 B hB hF]
  rw [originalMerge223, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
