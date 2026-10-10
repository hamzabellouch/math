import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData50
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound49
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound50
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound51

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1600 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1600 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1600 (originalVector B) := by
  rw [reducedMerge1600Check, Integer.Sparse.eval_mergeBy, reducedTermEval1604 B hB hF, reducedMergeEval1599 B hB hF]
  rw [originalMerge1600, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1601 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1601 (originalVector B) := by
  rw [reducedMerge1601Check, Integer.Sparse.eval_mergeBy, reducedTermEval1607 B hB hF, reducedTermEval1608 B hB hF]
  rw [originalMerge1601, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1602 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1602 (originalVector B) := by
  rw [reducedMerge1602Check, Integer.Sparse.eval_mergeBy, reducedTermEval1609 B hB hF, reducedTermEval1610 B hB hF]
  rw [originalMerge1602, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1603 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1603 (originalVector B) := by
  rw [reducedMerge1603Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1601 B hB hF, reducedMergeEval1602 B hB hF]
  rw [originalMerge1603, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1604 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1604 (originalVector B) := by
  rw [reducedMerge1604Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1600 B hB hF, reducedMergeEval1603 B hB hF]
  rw [originalMerge1604, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1605 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1605 (originalVector B) := by
  rw [reducedMerge1605Check, Integer.Sparse.eval_mergeBy, reducedTermEval1611 B hB hF, reducedTermEval1612 B hB hF]
  rw [originalMerge1605, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1606 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1606 (originalVector B) := by
  rw [reducedMerge1606Check, Integer.Sparse.eval_mergeBy, reducedTermEval1613 B hB hF, reducedTermEval1614 B hB hF]
  rw [originalMerge1606, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1607 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1607 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1607 (originalVector B) := by
  rw [reducedMerge1607Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1605 B hB hF, reducedMergeEval1606 B hB hF]
  rw [originalMerge1607, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1608 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1608 (originalVector B) := by
  rw [reducedMerge1608Check, Integer.Sparse.eval_mergeBy, reducedTermEval1615 B hB hF, reducedTermEval1616 B hB hF]
  rw [originalMerge1608, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1609 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1609 (originalVector B) := by
  rw [reducedMerge1609Check, Integer.Sparse.eval_mergeBy, reducedTermEval1617 B hB hF, reducedTermEval1618 B hB hF]
  rw [originalMerge1609, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1610 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1610 (originalVector B) := by
  rw [reducedMerge1610Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1608 B hB hF, reducedMergeEval1609 B hB hF]
  rw [originalMerge1610, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1611 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1611 (originalVector B) := by
  rw [reducedMerge1611Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1607 B hB hF, reducedMergeEval1610 B hB hF]
  rw [originalMerge1611, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1612 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1612 (originalVector B) := by
  rw [reducedMerge1612Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1604 B hB hF, reducedMergeEval1611 B hB hF]
  rw [originalMerge1612, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1613 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1613 (originalVector B) := by
  rw [reducedMerge1613Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1598 B hB hF, reducedMergeEval1612 B hB hF]
  rw [originalMerge1613, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1614 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1614 (originalVector B) := by
  rw [reducedMerge1614Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1584 B hB hF, reducedMergeEval1613 B hB hF]
  rw [originalMerge1614, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1615 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1615 (originalVector B) := by
  rw [reducedMerge1615Check, Integer.Sparse.eval_mergeBy, reducedTermEval1620 B hB hF, reducedTermEval1621 B hB hF]
  rw [originalMerge1615, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1616 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1616 (originalVector B) := by
  rw [reducedMerge1616Check, Integer.Sparse.eval_mergeBy, reducedTermEval1619 B hB hF, reducedMergeEval1615 B hB hF]
  rw [originalMerge1616, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1617 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1617 (originalVector B) := by
  rw [reducedMerge1617Check, Integer.Sparse.eval_mergeBy, reducedTermEval1622 B hB hF, reducedTermEval1623 B hB hF]
  rw [originalMerge1617, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1618 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1618 (originalVector B) := by
  rw [reducedMerge1618Check, Integer.Sparse.eval_mergeBy, reducedTermEval1624 B hB hF, reducedTermEval1625 B hB hF]
  rw [originalMerge1618, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1619 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1619 (originalVector B) := by
  rw [reducedMerge1619Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1617 B hB hF, reducedMergeEval1618 B hB hF]
  rw [originalMerge1619, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1620 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1620 (originalVector B) := by
  rw [reducedMerge1620Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1616 B hB hF, reducedMergeEval1619 B hB hF]
  rw [originalMerge1620, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1621 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1621 (originalVector B) := by
  rw [reducedMerge1621Check, Integer.Sparse.eval_mergeBy, reducedTermEval1626 B hB hF, reducedTermEval1627 B hB hF]
  rw [originalMerge1621, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1622 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1622 (originalVector B) := by
  rw [reducedMerge1622Check, Integer.Sparse.eval_mergeBy, reducedTermEval1628 B hB hF, reducedTermEval1629 B hB hF]
  rw [originalMerge1622, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1623 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1623 (originalVector B) := by
  rw [reducedMerge1623Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1621 B hB hF, reducedMergeEval1622 B hB hF]
  rw [originalMerge1623, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1624 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1624 (originalVector B) := by
  rw [reducedMerge1624Check, Integer.Sparse.eval_mergeBy, reducedTermEval1630 B hB hF, reducedTermEval1631 B hB hF]
  rw [originalMerge1624, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1625 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1625 (originalVector B) := by
  rw [reducedMerge1625Check, Integer.Sparse.eval_mergeBy, reducedTermEval1632 B hB hF, reducedTermEval1633 B hB hF]
  rw [originalMerge1625, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1626 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1626 (originalVector B) := by
  rw [reducedMerge1626Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1624 B hB hF, reducedMergeEval1625 B hB hF]
  rw [originalMerge1626, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1627 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1627 (originalVector B) := by
  rw [reducedMerge1627Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1623 B hB hF, reducedMergeEval1626 B hB hF]
  rw [originalMerge1627, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1628 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1628 (originalVector B) := by
  rw [reducedMerge1628Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1620 B hB hF, reducedMergeEval1627 B hB hF]
  rw [originalMerge1628, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1629 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1629 (originalVector B) := by
  rw [reducedMerge1629Check, Integer.Sparse.eval_mergeBy, reducedTermEval1635 B hB hF, reducedTermEval1636 B hB hF]
  rw [originalMerge1629, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1630 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1630 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1630 (originalVector B) := by
  rw [reducedMerge1630Check, Integer.Sparse.eval_mergeBy, reducedTermEval1634 B hB hF, reducedMergeEval1629 B hB hF]
  rw [originalMerge1630, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1631 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1631 (originalVector B) := by
  rw [reducedMerge1631Check, Integer.Sparse.eval_mergeBy, reducedTermEval1637 B hB hF, reducedTermEval1638 B hB hF]
  rw [originalMerge1631, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
