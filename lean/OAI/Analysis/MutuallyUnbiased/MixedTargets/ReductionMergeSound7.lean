import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData7
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound3
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound5
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound6
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound7
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound8

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval224 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge224 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge224 (originalVector B) := by
  rw [reducedMerge224Check, Integer.Sparse.eval_mergeBy, reducedMergeEval222 B hB hF, reducedMergeEval223 B hB hF]
  rw [originalMerge224, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval225 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge225 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge225 (originalVector B) := by
  rw [reducedMerge225Check, Integer.Sparse.eval_mergeBy, reducedMergeEval221 B hB hF, reducedMergeEval224 B hB hF]
  rw [originalMerge225, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval226 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge226 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge226 (originalVector B) := by
  rw [reducedMerge226Check, Integer.Sparse.eval_mergeBy, reducedTermEval231 B hB hF, reducedTermEval232 B hB hF]
  rw [originalMerge226, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge227 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge227 (originalVector B) := by
  rw [reducedMerge227Check, Integer.Sparse.eval_mergeBy, reducedTermEval233 B hB hF, reducedTermEval234 B hB hF]
  rw [originalMerge227, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge228 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge228 (originalVector B) := by
  rw [reducedMerge228Check, Integer.Sparse.eval_mergeBy, reducedMergeEval226 B hB hF, reducedMergeEval227 B hB hF]
  rw [originalMerge228, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge229 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge229 (originalVector B) := by
  rw [reducedMerge229Check, Integer.Sparse.eval_mergeBy, reducedTermEval235 B hB hF, reducedTermEval236 B hB hF]
  rw [originalMerge229, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge230 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge230 (originalVector B) := by
  rw [reducedMerge230Check, Integer.Sparse.eval_mergeBy, reducedTermEval237 B hB hF, reducedTermEval238 B hB hF]
  rw [originalMerge230, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval231 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge231 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge231 (originalVector B) := by
  rw [reducedMerge231Check, Integer.Sparse.eval_mergeBy, reducedMergeEval229 B hB hF, reducedMergeEval230 B hB hF]
  rw [originalMerge231, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval232 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge232 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge232 (originalVector B) := by
  rw [reducedMerge232Check, Integer.Sparse.eval_mergeBy, reducedMergeEval228 B hB hF, reducedMergeEval231 B hB hF]
  rw [originalMerge232, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval233 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge233 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge233 (originalVector B) := by
  rw [reducedMerge233Check, Integer.Sparse.eval_mergeBy, reducedMergeEval225 B hB hF, reducedMergeEval232 B hB hF]
  rw [originalMerge233, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval234 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge234 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge234 (originalVector B) := by
  rw [reducedMerge234Check, Integer.Sparse.eval_mergeBy, reducedMergeEval219 B hB hF, reducedMergeEval233 B hB hF]
  rw [originalMerge234, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval235 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge235 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge235 (originalVector B) := by
  rw [reducedMerge235Check, Integer.Sparse.eval_mergeBy, reducedMergeEval205 B hB hF, reducedMergeEval234 B hB hF]
  rw [originalMerge235, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval236 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge236 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge236 (originalVector B) := by
  rw [reducedMerge236Check, Integer.Sparse.eval_mergeBy, reducedMergeEval176 B hB hF, reducedMergeEval235 B hB hF]
  rw [originalMerge236, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval237 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge237 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge237 (originalVector B) := by
  rw [reducedMerge237Check, Integer.Sparse.eval_mergeBy, reducedMergeEval117 B hB hF, reducedMergeEval236 B hB hF]
  rw [originalMerge237, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval238 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge238 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge238 (originalVector B) := by
  rw [reducedMerge238Check, Integer.Sparse.eval_mergeBy, reducedTermEval240 B hB hF, reducedTermEval241 B hB hF]
  rw [originalMerge238, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval239 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge239 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge239 (originalVector B) := by
  rw [reducedMerge239Check, Integer.Sparse.eval_mergeBy, reducedTermEval239 B hB hF, reducedMergeEval238 B hB hF]
  rw [originalMerge239, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval240 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge240 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge240 (originalVector B) := by
  rw [reducedMerge240Check, Integer.Sparse.eval_mergeBy, reducedTermEval242 B hB hF, reducedTermEval243 B hB hF]
  rw [originalMerge240, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval241 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge241 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge241 (originalVector B) := by
  rw [reducedMerge241Check, Integer.Sparse.eval_mergeBy, reducedTermEval244 B hB hF, reducedTermEval245 B hB hF]
  rw [originalMerge241, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval242 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge242 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge242 (originalVector B) := by
  rw [reducedMerge242Check, Integer.Sparse.eval_mergeBy, reducedMergeEval240 B hB hF, reducedMergeEval241 B hB hF]
  rw [originalMerge242, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge243 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge243 (originalVector B) := by
  rw [reducedMerge243Check, Integer.Sparse.eval_mergeBy, reducedMergeEval239 B hB hF, reducedMergeEval242 B hB hF]
  rw [originalMerge243, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval244 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge244 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge244 (originalVector B) := by
  rw [reducedMerge244Check, Integer.Sparse.eval_mergeBy, reducedTermEval246 B hB hF, reducedTermEval247 B hB hF]
  rw [originalMerge244, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval245 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge245 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge245 (originalVector B) := by
  rw [reducedMerge245Check, Integer.Sparse.eval_mergeBy, reducedTermEval248 B hB hF, reducedTermEval249 B hB hF]
  rw [originalMerge245, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval246 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge246 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge246 (originalVector B) := by
  rw [reducedMerge246Check, Integer.Sparse.eval_mergeBy, reducedMergeEval244 B hB hF, reducedMergeEval245 B hB hF]
  rw [originalMerge246, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval247 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge247 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge247 (originalVector B) := by
  rw [reducedMerge247Check, Integer.Sparse.eval_mergeBy, reducedTermEval250 B hB hF, reducedTermEval251 B hB hF]
  rw [originalMerge247, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval248 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge248 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge248 (originalVector B) := by
  rw [reducedMerge248Check, Integer.Sparse.eval_mergeBy, reducedTermEval252 B hB hF, reducedTermEval253 B hB hF]
  rw [originalMerge248, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval249 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge249 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge249 (originalVector B) := by
  rw [reducedMerge249Check, Integer.Sparse.eval_mergeBy, reducedMergeEval247 B hB hF, reducedMergeEval248 B hB hF]
  rw [originalMerge249, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval250 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge250 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge250 (originalVector B) := by
  rw [reducedMerge250Check, Integer.Sparse.eval_mergeBy, reducedMergeEval246 B hB hF, reducedMergeEval249 B hB hF]
  rw [originalMerge250, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval251 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge251 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge251 (originalVector B) := by
  rw [reducedMerge251Check, Integer.Sparse.eval_mergeBy, reducedMergeEval243 B hB hF, reducedMergeEval250 B hB hF]
  rw [originalMerge251, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval252 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge252 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge252 (originalVector B) := by
  rw [reducedMerge252Check, Integer.Sparse.eval_mergeBy, reducedTermEval255 B hB hF, reducedTermEval256 B hB hF]
  rw [originalMerge252, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval253 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge253 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge253 (originalVector B) := by
  rw [reducedMerge253Check, Integer.Sparse.eval_mergeBy, reducedTermEval254 B hB hF, reducedMergeEval252 B hB hF]
  rw [originalMerge253, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval254 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge254 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge254 (originalVector B) := by
  rw [reducedMerge254Check, Integer.Sparse.eval_mergeBy, reducedTermEval257 B hB hF, reducedTermEval258 B hB hF]
  rw [originalMerge254, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval255 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge255 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge255 (originalVector B) := by
  rw [reducedMerge255Check, Integer.Sparse.eval_mergeBy, reducedTermEval259 B hB hF, reducedTermEval260 B hB hF]
  rw [originalMerge255, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
