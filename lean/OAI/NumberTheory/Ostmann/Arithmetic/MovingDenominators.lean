import OAI.NumberTheory.Ostmann.Arithmetic.MovingTopCells

namespace OAI

/-! # The actual cleared denominators in a moving history -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotReversal.giantFormula_denominator {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) :
    (step.giantFormula value hs hu L R).cleared.denominator =
      step.rootFrequency * (MovingSlotReversal.naturalProduct value step.compensationSlots : ℤ) *
        L.cleared.denominator * R.cleared.denominator := by
  simp only [giantFormula, HistoryFormula.cleared, ClearedHistoryValue.pivot,
    ClearedHistoryValue.prod, ClearedHistoryValue.constant, Fintype.prod_bool,
    Bool.false_eq_true, ite_false, ite_true, mul_one]

theorem movingNodeGuard_denominators (CL CR : ℕ) (s v w : ℤ) (hs : s ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) :
    (movingNodeGuard CL CR s v w hs childBound pivotBound L R).pivot.cleared.denominator =
        s * L.cleared.denominator * R.cleared.denominator ∧
      (movingNodeGuard CL CR s v w hs childBound pivotBound L R).rightProduct.cleared.denominator =
        R.cleared.denominator := by
  simp [movingNodeGuard, wordTransferGuard, wordTransferStep, movingNodeWord,
    HistoryPivotStep.formula, HistoryFormula.bind, HistoryFormula.listProduct,
    HistoryFormula.cleared, ClearedHistoryValue.pivot, ClearedHistoryValue.prod,
    ClearedHistoryValue.constant]

/-- The three residue tests cost only powers of the existing ancestor
 denominators, one compensation product, and the actual node frequencies. -/
theorem movingNode_residuePeriod {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) :
    ({ guard := movingNodeGuard (MovingSlotReversal.naturalProduct value step.leftSlots)
          (MovingSlotReversal.naturalProduct value step.rightSlots)
          step.rootFrequency step.leftFrequency step.rightFrequency hs childBound pivotBound L R
       newGiant := step.giantFormula value hs hu L R } : MovingFormulaNode).residuePeriod =
      step.rootFrequency.natAbs ^ 3 * step.rightFrequency.natAbs *
        MovingSlotReversal.naturalProduct value step.compensationSlots *
        L.cleared.denominator.natAbs ^ 2 * R.cleared.denominator.natAbs ^ 3 := by
  have hg := movingNodeGuard_denominators (MovingSlotReversal.naturalProduct value step.leftSlots)
    (MovingSlotReversal.naturalProduct value step.rightSlots) step.rootFrequency
    step.leftFrequency step.rightFrequency hs childBound pivotBound L R
  simp only [MovingFormulaNode.residuePeriod, MovingFormulaNode.testFormulas,
    MovingFormulaNode.testModuli, Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.prod_univ_zero, mul_one]
  rw [hg.1, hg.2, step.giantFormula_denominator value hs hu L R]
  simp only [movingNodeGuard, wordTransferGuard, Int.natAbs_mul, Int.natAbs_natCast]
  ring

end Ostmann

end OAI
