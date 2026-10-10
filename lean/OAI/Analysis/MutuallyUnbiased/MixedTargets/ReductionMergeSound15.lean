import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData15
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound14
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound15
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound16

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval480 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge480 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge480 (originalVector B) := by
  rw [reducedMerge480Check, Integer.Sparse.eval_mergeBy, reducedTermEval482 B hB hF, reducedTermEval483 B hB hF]
  rw [originalMerge480, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval481 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge481 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge481 (originalVector B) := by
  rw [reducedMerge481Check, Integer.Sparse.eval_mergeBy, reducedTermEval484 B hB hF, reducedTermEval485 B hB hF]
  rw [originalMerge481, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval482 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge482 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge482 (originalVector B) := by
  rw [reducedMerge482Check, Integer.Sparse.eval_mergeBy, reducedMergeEval480 B hB hF, reducedMergeEval481 B hB hF]
  rw [originalMerge482, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval483 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge483 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge483 (originalVector B) := by
  rw [reducedMerge483Check, Integer.Sparse.eval_mergeBy, reducedMergeEval479 B hB hF, reducedMergeEval482 B hB hF]
  rw [originalMerge483, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval484 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge484 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge484 (originalVector B) := by
  rw [reducedMerge484Check, Integer.Sparse.eval_mergeBy, reducedTermEval486 B hB hF, reducedTermEval487 B hB hF]
  rw [originalMerge484, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge485 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge485 (originalVector B) := by
  rw [reducedMerge485Check, Integer.Sparse.eval_mergeBy, reducedTermEval488 B hB hF, reducedTermEval489 B hB hF]
  rw [originalMerge485, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge486 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge486 (originalVector B) := by
  rw [reducedMerge486Check, Integer.Sparse.eval_mergeBy, reducedMergeEval484 B hB hF, reducedMergeEval485 B hB hF]
  rw [originalMerge486, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval487 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge487 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge487 (originalVector B) := by
  rw [reducedMerge487Check, Integer.Sparse.eval_mergeBy, reducedTermEval490 B hB hF, reducedTermEval491 B hB hF]
  rw [originalMerge487, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval488 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge488 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge488 (originalVector B) := by
  rw [reducedMerge488Check, Integer.Sparse.eval_mergeBy, reducedTermEval492 B hB hF, reducedTermEval493 B hB hF]
  rw [originalMerge488, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval489 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge489 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge489 (originalVector B) := by
  rw [reducedMerge489Check, Integer.Sparse.eval_mergeBy, reducedMergeEval487 B hB hF, reducedMergeEval488 B hB hF]
  rw [originalMerge489, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval490 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge490 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge490 (originalVector B) := by
  rw [reducedMerge490Check, Integer.Sparse.eval_mergeBy, reducedMergeEval486 B hB hF, reducedMergeEval489 B hB hF]
  rw [originalMerge490, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval491 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge491 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge491 (originalVector B) := by
  rw [reducedMerge491Check, Integer.Sparse.eval_mergeBy, reducedMergeEval483 B hB hF, reducedMergeEval490 B hB hF]
  rw [originalMerge491, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval492 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge492 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge492 (originalVector B) := by
  rw [reducedMerge492Check, Integer.Sparse.eval_mergeBy, reducedTermEval495 B hB hF, reducedTermEval496 B hB hF]
  rw [originalMerge492, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval493 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge493 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge493 (originalVector B) := by
  rw [reducedMerge493Check, Integer.Sparse.eval_mergeBy, reducedTermEval494 B hB hF, reducedMergeEval492 B hB hF]
  rw [originalMerge493, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval494 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge494 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge494 (originalVector B) := by
  rw [reducedMerge494Check, Integer.Sparse.eval_mergeBy, reducedTermEval497 B hB hF, reducedTermEval498 B hB hF]
  rw [originalMerge494, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge495 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge495 (originalVector B) := by
  rw [reducedMerge495Check, Integer.Sparse.eval_mergeBy, reducedTermEval499 B hB hF, reducedTermEval500 B hB hF]
  rw [originalMerge495, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge496 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge496 (originalVector B) := by
  rw [reducedMerge496Check, Integer.Sparse.eval_mergeBy, reducedMergeEval494 B hB hF, reducedMergeEval495 B hB hF]
  rw [originalMerge496, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge497 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge497 (originalVector B) := by
  rw [reducedMerge497Check, Integer.Sparse.eval_mergeBy, reducedMergeEval493 B hB hF, reducedMergeEval496 B hB hF]
  rw [originalMerge497, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge498 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge498 (originalVector B) := by
  rw [reducedMerge498Check, Integer.Sparse.eval_mergeBy, reducedTermEval501 B hB hF, reducedTermEval502 B hB hF]
  rw [originalMerge498, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval499 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge499 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge499 (originalVector B) := by
  rw [reducedMerge499Check, Integer.Sparse.eval_mergeBy, reducedTermEval503 B hB hF, reducedTermEval504 B hB hF]
  rw [originalMerge499, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval500 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge500 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge500 (originalVector B) := by
  rw [reducedMerge500Check, Integer.Sparse.eval_mergeBy, reducedMergeEval498 B hB hF, reducedMergeEval499 B hB hF]
  rw [originalMerge500, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge501 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge501 (originalVector B) := by
  rw [reducedMerge501Check, Integer.Sparse.eval_mergeBy, reducedTermEval505 B hB hF, reducedTermEval506 B hB hF]
  rw [originalMerge501, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge502 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge502 (originalVector B) := by
  rw [reducedMerge502Check, Integer.Sparse.eval_mergeBy, reducedTermEval507 B hB hF, reducedTermEval508 B hB hF]
  rw [originalMerge502, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval503 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge503 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge503 (originalVector B) := by
  rw [reducedMerge503Check, Integer.Sparse.eval_mergeBy, reducedMergeEval501 B hB hF, reducedMergeEval502 B hB hF]
  rw [originalMerge503, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval504 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge504 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge504 (originalVector B) := by
  rw [reducedMerge504Check, Integer.Sparse.eval_mergeBy, reducedMergeEval500 B hB hF, reducedMergeEval503 B hB hF]
  rw [originalMerge504, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge505 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge505 (originalVector B) := by
  rw [reducedMerge505Check, Integer.Sparse.eval_mergeBy, reducedMergeEval497 B hB hF, reducedMergeEval504 B hB hF]
  rw [originalMerge505, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval506 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge506 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge506 (originalVector B) := by
  rw [reducedMerge506Check, Integer.Sparse.eval_mergeBy, reducedMergeEval491 B hB hF, reducedMergeEval505 B hB hF]
  rw [originalMerge506, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval507 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge507 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge507 (originalVector B) := by
  rw [reducedMerge507Check, Integer.Sparse.eval_mergeBy, reducedTermEval510 B hB hF, reducedTermEval511 B hB hF]
  rw [originalMerge507, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval508 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge508 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge508 (originalVector B) := by
  rw [reducedMerge508Check, Integer.Sparse.eval_mergeBy, reducedTermEval509 B hB hF, reducedMergeEval507 B hB hF]
  rw [originalMerge508, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval509 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge509 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge509 (originalVector B) := by
  rw [reducedMerge509Check, Integer.Sparse.eval_mergeBy, reducedTermEval512 B hB hF, reducedTermEval513 B hB hF]
  rw [originalMerge509, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval510 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge510 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge510 (originalVector B) := by
  rw [reducedMerge510Check, Integer.Sparse.eval_mergeBy, reducedTermEval514 B hB hF, reducedTermEval515 B hB hF]
  rw [originalMerge510, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge511 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge511 (originalVector B) := by
  rw [reducedMerge511Check, Integer.Sparse.eval_mergeBy, reducedMergeEval509 B hB hF, reducedMergeEval510 B hB hF]
  rw [originalMerge511, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
