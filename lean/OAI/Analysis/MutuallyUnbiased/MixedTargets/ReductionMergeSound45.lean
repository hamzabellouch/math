import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData45
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound44
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound45
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound46

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1440 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1440 (originalVector B) := by
  rw [reducedMerge1440Check, Integer.Sparse.eval_mergeBy, reducedTermEval1444 B hB hF, reducedTermEval1445 B hB hF]
  rw [originalMerge1440, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1441 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1441 (originalVector B) := by
  rw [reducedMerge1441Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1439 B hB hF, reducedMergeEval1440 B hB hF]
  rw [originalMerge1441, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1442 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1442 (originalVector B) := by
  rw [reducedMerge1442Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1438 B hB hF, reducedMergeEval1441 B hB hF]
  rw [originalMerge1442, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1443 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1443 (originalVector B) := by
  rw [reducedMerge1443Check, Integer.Sparse.eval_mergeBy, reducedTermEval1446 B hB hF, reducedTermEval1447 B hB hF]
  rw [originalMerge1443, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1444 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1444 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1444 (originalVector B) := by
  rw [reducedMerge1444Check, Integer.Sparse.eval_mergeBy, reducedTermEval1448 B hB hF, reducedTermEval1449 B hB hF]
  rw [originalMerge1444, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1445 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1445 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1445 (originalVector B) := by
  rw [reducedMerge1445Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1443 B hB hF, reducedMergeEval1444 B hB hF]
  rw [originalMerge1445, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1446 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1446 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1446 (originalVector B) := by
  rw [reducedMerge1446Check, Integer.Sparse.eval_mergeBy, reducedTermEval1450 B hB hF, reducedTermEval1451 B hB hF]
  rw [originalMerge1446, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1447 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1447 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1447 (originalVector B) := by
  rw [reducedMerge1447Check, Integer.Sparse.eval_mergeBy, reducedTermEval1452 B hB hF, reducedTermEval1453 B hB hF]
  rw [originalMerge1447, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1448 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1448 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1448 (originalVector B) := by
  rw [reducedMerge1448Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1446 B hB hF, reducedMergeEval1447 B hB hF]
  rw [originalMerge1448, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1449 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1449 (originalVector B) := by
  rw [reducedMerge1449Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1445 B hB hF, reducedMergeEval1448 B hB hF]
  rw [originalMerge1449, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1450 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1450 (originalVector B) := by
  rw [reducedMerge1450Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1442 B hB hF, reducedMergeEval1449 B hB hF]
  rw [originalMerge1450, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1451 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1451 (originalVector B) := by
  rw [reducedMerge1451Check, Integer.Sparse.eval_mergeBy, reducedTermEval1455 B hB hF, reducedTermEval1456 B hB hF]
  rw [originalMerge1451, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1452 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1452 (originalVector B) := by
  rw [reducedMerge1452Check, Integer.Sparse.eval_mergeBy, reducedTermEval1454 B hB hF, reducedMergeEval1451 B hB hF]
  rw [originalMerge1452, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1453 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1453 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1453 (originalVector B) := by
  rw [reducedMerge1453Check, Integer.Sparse.eval_mergeBy, reducedTermEval1457 B hB hF, reducedTermEval1458 B hB hF]
  rw [originalMerge1453, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1454 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1454 (originalVector B) := by
  rw [reducedMerge1454Check, Integer.Sparse.eval_mergeBy, reducedTermEval1459 B hB hF, reducedTermEval1460 B hB hF]
  rw [originalMerge1454, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1455 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1455 (originalVector B) := by
  rw [reducedMerge1455Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1453 B hB hF, reducedMergeEval1454 B hB hF]
  rw [originalMerge1455, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1456 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1456 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1456 (originalVector B) := by
  rw [reducedMerge1456Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1452 B hB hF, reducedMergeEval1455 B hB hF]
  rw [originalMerge1456, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1457 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1457 (originalVector B) := by
  rw [reducedMerge1457Check, Integer.Sparse.eval_mergeBy, reducedTermEval1461 B hB hF, reducedTermEval1462 B hB hF]
  rw [originalMerge1457, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1458 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1458 (originalVector B) := by
  rw [reducedMerge1458Check, Integer.Sparse.eval_mergeBy, reducedTermEval1463 B hB hF, reducedTermEval1464 B hB hF]
  rw [originalMerge1458, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1459 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1459 (originalVector B) := by
  rw [reducedMerge1459Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1457 B hB hF, reducedMergeEval1458 B hB hF]
  rw [originalMerge1459, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1460 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1460 (originalVector B) := by
  rw [reducedMerge1460Check, Integer.Sparse.eval_mergeBy, reducedTermEval1465 B hB hF, reducedTermEval1466 B hB hF]
  rw [originalMerge1460, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1461 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1461 (originalVector B) := by
  rw [reducedMerge1461Check, Integer.Sparse.eval_mergeBy, reducedTermEval1467 B hB hF, reducedTermEval1468 B hB hF]
  rw [originalMerge1461, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1462 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1462 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1462 (originalVector B) := by
  rw [reducedMerge1462Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1460 B hB hF, reducedMergeEval1461 B hB hF]
  rw [originalMerge1462, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1463 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1463 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1463 (originalVector B) := by
  rw [reducedMerge1463Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1459 B hB hF, reducedMergeEval1462 B hB hF]
  rw [originalMerge1463, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1464 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1464 (originalVector B) := by
  rw [reducedMerge1464Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1456 B hB hF, reducedMergeEval1463 B hB hF]
  rw [originalMerge1464, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1465 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1465 (originalVector B) := by
  rw [reducedMerge1465Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1450 B hB hF, reducedMergeEval1464 B hB hF]
  rw [originalMerge1465, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1466 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1466 (originalVector B) := by
  rw [reducedMerge1466Check, Integer.Sparse.eval_mergeBy, reducedTermEval1470 B hB hF, reducedTermEval1471 B hB hF]
  rw [originalMerge1466, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1467 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1467 (originalVector B) := by
  rw [reducedMerge1467Check, Integer.Sparse.eval_mergeBy, reducedTermEval1469 B hB hF, reducedMergeEval1466 B hB hF]
  rw [originalMerge1467, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1468 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1468 (originalVector B) := by
  rw [reducedMerge1468Check, Integer.Sparse.eval_mergeBy, reducedTermEval1472 B hB hF, reducedTermEval1473 B hB hF]
  rw [originalMerge1468, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1469 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1469 (originalVector B) := by
  rw [reducedMerge1469Check, Integer.Sparse.eval_mergeBy, reducedTermEval1474 B hB hF, reducedTermEval1475 B hB hF]
  rw [originalMerge1469, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1470 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1470 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1470 (originalVector B) := by
  rw [reducedMerge1470Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1468 B hB hF, reducedMergeEval1469 B hB hF]
  rw [originalMerge1470, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1471 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1471 (originalVector B) := by
  rw [reducedMerge1471Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1467 B hB hF, reducedMergeEval1470 B hB hF]
  rw [originalMerge1471, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
