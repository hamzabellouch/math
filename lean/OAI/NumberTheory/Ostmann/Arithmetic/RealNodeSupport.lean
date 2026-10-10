import OAI.NumberTheory.Ostmann.Construction.HistoryRealEvaluation
import OAI.NumberTheory.Ostmann.Arithmetic.RealSlotEvaluation

namespace OAI

/-! # The original real node inequalities with variable bulk values -/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotReversal.realCompositePivot {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (L R : ℝ) : ℝ :=
  ((s.leftFrequency : ℝ) * realSlotProduct value s.rightSlots * R -
    (s.rightFrequency : ℝ) * realSlotProduct value s.leftSlots * L) / s.rootFrequency

noncomputable def realValueNodeSupport {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) : {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → Prop
  | _, .leaf _ _, _, _ => True
  | n + 1, .node s CL CR u left right, L, R =>
      let step := MovingSlotData.step s CL CR u left right false
      let Q := step.realCompositePivot value L R
      let p := step.realValuePivot value L R
      1 ≤ Q ∧ Q ≤ pivotBound (n + 1) ∧
        ((2 * pivotBound (n + 1) * childBound (n + 1) + 1 : ℕ) : ℝ) ≤
          R * realSlotProduct value CR ∧
        realValueNodeSupport value childBound pivotBound left p L ∧
        realValueNodeSupport value childBound pivotBound right p R

theorem MovingSlotReversal.giantFormula_realEval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (hs : s.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value s.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    (s.giantFormula value hs hu L R).realEval x =
      s.realValuePivot (fun i => (value i : ℝ)) (L.realEval x) (R.realEval x) := by
  simp only [giantFormula, HistoryFormula.realEval_solve, HistoryFormula.realEval_product,
    HistoryFormula.realEval_external, Int.cast_mul, Int.cast_natCast, realValuePivot,
    realSlotProduct_nat]
  ring

theorem movingNodeGuard_realEval (CL CR : ℕ) (s v w : ℤ) (hs : s ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    (movingNodeGuard CL CR s v w hs childBound pivotBound L R).archimedeanAt x ↔
      1 ≤ ((v : ℝ) * (CR : ℝ) * R.realEval x - (w : ℝ) * (CL : ℝ) * L.realEval x) / s ∧
      ((v : ℝ) * (CR : ℝ) * R.realEval x - (w : ℝ) * (CL : ℝ) * L.realEval x) / s ≤ pivotBound ∧
      ((2 * pivotBound * childBound + 1 : ℕ) : ℝ) ≤ R.realEval x * CR := by
  simp only [movingNodeGuard, wordTransferGuard, WordTransferGuard.archimedeanAt,
    HistoryFormula.realEval_bind, HistoryPivotStep.formula, wordTransferStep, movingNodeWord,
    HistoryFormula.realEval_solve, HistoryFormula.realEval_listProduct, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, HistoryFormula.realEval_prime, Bool.false_eq_true, ite_false,
    ite_true, HistoryFormula.realEval_product, HistoryFormula.realEval_external, Int.cast_natCast, mul_one]
  ring_nf

/-- Exact agreement with all original archimedean formula-node tests. -/
theorem realValueNodeSupport_nat {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    movingArchimedeanGate (T.formulaNodes value hvalue childBound pivotBound hf L R) x ↔
      realValueNodeSupport (fun i => (value i : ℝ)) childBound pivotBound T (L.realEval x) (R.realEval x) := by
  induction T generalizing L R with
  | leaf => simp [MovingSlotData.formulaNodes, movingArchimedeanGate, realValueNodeSupport]
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.formulaNodes, movingArchimedeanGate, List.forall_mem_cons,
      List.forall_mem_append, realValueNodeSupport]
    rw [show (∀ f ∈ left.formulaNodes value hvalue childBound pivotBound hf.2.1
          ((MovingSlotData.step s CL CR u left right false).giantFormula value hf.1
            (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R) L, f.guard.archimedeanAt x) ↔ _ from
      ihL hf.2.1 _ L,
      show (∀ f ∈ right.formulaNodes value hvalue childBound pivotBound hf.2.2
          ((MovingSlotData.step s CL CR u left right false).giantFormula value hf.1
            (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R) R, f.guard.archimedeanAt x) ↔ _ from
      ihR hf.2.2 _ R]
    rw [movingNodeGuard_realEval]
    simp only [MovingSlotReversal.giantFormula_realEval, MovingSlotReversal.realCompositePivot,
      MovingSlotData.step, realSlotProduct_nat]
    tauto

end Ostmann

end OAI
