import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData16
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound15
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound16
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound17

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval512 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge512 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge512 (originalVector B) := by
  rw [reducedMerge512Check, Integer.Sparse.eval_mergeBy, reducedMergeEval508 B hB hF, reducedMergeEval511 B hB hF]
  rw [originalMerge512, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval513 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge513 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge513 (originalVector B) := by
  rw [reducedMerge513Check, Integer.Sparse.eval_mergeBy, reducedTermEval516 B hB hF, reducedTermEval517 B hB hF]
  rw [originalMerge513, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval514 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge514 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge514 (originalVector B) := by
  rw [reducedMerge514Check, Integer.Sparse.eval_mergeBy, reducedTermEval518 B hB hF, reducedTermEval519 B hB hF]
  rw [originalMerge514, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval515 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge515 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge515 (originalVector B) := by
  rw [reducedMerge515Check, Integer.Sparse.eval_mergeBy, reducedMergeEval513 B hB hF, reducedMergeEval514 B hB hF]
  rw [originalMerge515, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval516 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge516 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge516 (originalVector B) := by
  rw [reducedMerge516Check, Integer.Sparse.eval_mergeBy, reducedTermEval520 B hB hF, reducedTermEval521 B hB hF]
  rw [originalMerge516, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval517 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge517 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge517 (originalVector B) := by
  rw [reducedMerge517Check, Integer.Sparse.eval_mergeBy, reducedTermEval522 B hB hF, reducedTermEval523 B hB hF]
  rw [originalMerge517, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval518 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge518 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge518 (originalVector B) := by
  rw [reducedMerge518Check, Integer.Sparse.eval_mergeBy, reducedMergeEval516 B hB hF, reducedMergeEval517 B hB hF]
  rw [originalMerge518, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval519 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge519 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge519 (originalVector B) := by
  rw [reducedMerge519Check, Integer.Sparse.eval_mergeBy, reducedMergeEval515 B hB hF, reducedMergeEval518 B hB hF]
  rw [originalMerge519, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval520 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge520 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge520 (originalVector B) := by
  rw [reducedMerge520Check, Integer.Sparse.eval_mergeBy, reducedMergeEval512 B hB hF, reducedMergeEval519 B hB hF]
  rw [originalMerge520, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval521 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge521 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge521 (originalVector B) := by
  rw [reducedMerge521Check, Integer.Sparse.eval_mergeBy, reducedTermEval525 B hB hF, reducedTermEval526 B hB hF]
  rw [originalMerge521, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval522 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge522 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge522 (originalVector B) := by
  rw [reducedMerge522Check, Integer.Sparse.eval_mergeBy, reducedTermEval524 B hB hF, reducedMergeEval521 B hB hF]
  rw [originalMerge522, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval523 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge523 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge523 (originalVector B) := by
  rw [reducedMerge523Check, Integer.Sparse.eval_mergeBy, reducedTermEval527 B hB hF, reducedTermEval528 B hB hF]
  rw [originalMerge523, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval524 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge524 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge524 (originalVector B) := by
  rw [reducedMerge524Check, Integer.Sparse.eval_mergeBy, reducedTermEval529 B hB hF, reducedTermEval530 B hB hF]
  rw [originalMerge524, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval525 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge525 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge525 (originalVector B) := by
  rw [reducedMerge525Check, Integer.Sparse.eval_mergeBy, reducedMergeEval523 B hB hF, reducedMergeEval524 B hB hF]
  rw [originalMerge525, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval526 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge526 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge526 (originalVector B) := by
  rw [reducedMerge526Check, Integer.Sparse.eval_mergeBy, reducedMergeEval522 B hB hF, reducedMergeEval525 B hB hF]
  rw [originalMerge526, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval527 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge527 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge527 (originalVector B) := by
  rw [reducedMerge527Check, Integer.Sparse.eval_mergeBy, reducedTermEval531 B hB hF, reducedTermEval532 B hB hF]
  rw [originalMerge527, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval528 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge528 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge528 (originalVector B) := by
  rw [reducedMerge528Check, Integer.Sparse.eval_mergeBy, reducedTermEval533 B hB hF, reducedTermEval534 B hB hF]
  rw [originalMerge528, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval529 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge529 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge529 (originalVector B) := by
  rw [reducedMerge529Check, Integer.Sparse.eval_mergeBy, reducedMergeEval527 B hB hF, reducedMergeEval528 B hB hF]
  rw [originalMerge529, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval530 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge530 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge530 (originalVector B) := by
  rw [reducedMerge530Check, Integer.Sparse.eval_mergeBy, reducedTermEval535 B hB hF, reducedTermEval536 B hB hF]
  rw [originalMerge530, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval531 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge531 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge531 (originalVector B) := by
  rw [reducedMerge531Check, Integer.Sparse.eval_mergeBy, reducedTermEval537 B hB hF, reducedTermEval538 B hB hF]
  rw [originalMerge531, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval532 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge532 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge532 (originalVector B) := by
  rw [reducedMerge532Check, Integer.Sparse.eval_mergeBy, reducedMergeEval530 B hB hF, reducedMergeEval531 B hB hF]
  rw [originalMerge532, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval533 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge533 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge533 (originalVector B) := by
  rw [reducedMerge533Check, Integer.Sparse.eval_mergeBy, reducedMergeEval529 B hB hF, reducedMergeEval532 B hB hF]
  rw [originalMerge533, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval534 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge534 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge534 (originalVector B) := by
  rw [reducedMerge534Check, Integer.Sparse.eval_mergeBy, reducedMergeEval526 B hB hF, reducedMergeEval533 B hB hF]
  rw [originalMerge534, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval535 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge535 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge535 (originalVector B) := by
  rw [reducedMerge535Check, Integer.Sparse.eval_mergeBy, reducedMergeEval520 B hB hF, reducedMergeEval534 B hB hF]
  rw [originalMerge535, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval536 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge536 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge536 (originalVector B) := by
  rw [reducedMerge536Check, Integer.Sparse.eval_mergeBy, reducedMergeEval506 B hB hF, reducedMergeEval535 B hB hF]
  rw [originalMerge536, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval537 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge537 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge537 (originalVector B) := by
  rw [reducedMerge537Check, Integer.Sparse.eval_mergeBy, reducedTermEval540 B hB hF, reducedTermEval541 B hB hF]
  rw [originalMerge537, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval538 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge538 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge538 (originalVector B) := by
  rw [reducedMerge538Check, Integer.Sparse.eval_mergeBy, reducedTermEval539 B hB hF, reducedMergeEval537 B hB hF]
  rw [originalMerge538, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval539 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge539 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge539 (originalVector B) := by
  rw [reducedMerge539Check, Integer.Sparse.eval_mergeBy, reducedTermEval542 B hB hF, reducedTermEval543 B hB hF]
  rw [originalMerge539, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval540 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge540 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge540 (originalVector B) := by
  rw [reducedMerge540Check, Integer.Sparse.eval_mergeBy, reducedTermEval544 B hB hF, reducedTermEval545 B hB hF]
  rw [originalMerge540, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval541 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge541 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge541 (originalVector B) := by
  rw [reducedMerge541Check, Integer.Sparse.eval_mergeBy, reducedMergeEval539 B hB hF, reducedMergeEval540 B hB hF]
  rw [originalMerge541, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval542 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge542 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge542 (originalVector B) := by
  rw [reducedMerge542Check, Integer.Sparse.eval_mergeBy, reducedMergeEval538 B hB hF, reducedMergeEval541 B hB hF]
  rw [originalMerge542, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval543 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge543 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge543 (originalVector B) := by
  rw [reducedMerge543Check, Integer.Sparse.eval_mergeBy, reducedTermEval546 B hB hF, reducedTermEval547 B hB hF]
  rw [originalMerge543, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
