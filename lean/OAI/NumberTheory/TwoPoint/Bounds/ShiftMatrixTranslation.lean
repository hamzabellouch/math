import OAI.NumberTheory.TwoPoint.Bounds.ShiftedIntegerPaths

namespace OAI

/-! Translate the physical block coordinates without changing its
matrix. Arithmetic weights and the numerical gate use the same origin. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem physicalShiftMatrix_translate {D V : Type*}
    [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ) (c : ℤ) :
    shiftMatrix embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + c))) =
    shiftMatrix (fun i => ((embed i).1, (embed i).2 + c)) (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h (fun d n m => gate d (n - c) (m - c)) weight) := by
  ext i j
  apply sum_congr rfl
  intro e _
  have he : integerShiftNext Q tuple h e ((embed i).1, (embed i).2 + c) =
      ((embed j).1, (embed j).2 + c) ↔
      integerShiftNext Q tuple h e (embed i) = embed j := by
    rw [Prod.ext_iff, Prod.ext_iff]
    change (e.1 = (embed j).1 ∧ (embed i).2 + c +
      (SignedStep.mk e.2.2 (tuple e.1) e.2.1).displacement h = (embed j).2 + c) ↔
      (e.1 = (embed j).1 ∧ (embed i).2 +
      (SignedStep.mk e.2.2 (tuple e.1) e.2.1).displacement h = (embed j).2)
    constructor <;> rintro ⟨hd, hz⟩ <;> refine ⟨hd, ?_⟩ <;> omega
  have hw : physicalShiftWeight Q tuple h (fun d n m => gate d (n - c) (m - c)) weight
      e ((embed i).1, (embed i).2 + c) =
      physicalShiftWeight Q tuple h gate (fun t n => weight t (n + c)) e (embed i) := by
    have hs : (embed i).2 + c +
        (SignedStep.mk e.2.2 (tuple e.1) e.2.1).displacement h - c =
        (embed i).2 + (SignedStep.mk e.2.2 (tuple e.1) e.2.1).displacement h := by omega
    have hc : ((embed i).1 ≠ e.1 ∧
        gate e.1 (((embed i).2 + c) - c)
          ((integerShiftNext Q tuple h e ((embed i).1, (embed i).2 + c)).2 - c)) ↔
        ((embed i).1 ≠ e.1 ∧
        gate e.1 (embed i).2 (integerShiftNext Q tuple h e (embed i)).2) := by
      simp only [integerShiftNext, add_sub_cancel_right, hs]
    by_cases hg : (embed i).1 ≠ e.1 ∧
        gate e.1 (embed i).2 (integerShiftNext Q tuple h e (embed i)).2
    · simp only [physicalShiftWeight, ite_eq_left hg, ite_eq_left (hc.mpr hg)]
    · simp only [physicalShiftWeight, ite_eq_right hg, ite_eq_right (mt hc.mp hg)]
  simp only [he, hw]
  by_cases hc : integerShiftNext Q tuple h e (embed i) = embed j
  · simp only [ite_eq_left hc]
  · simp only [ite_eq_right hc]

theorem physicalBlockMatrix_eq_integer {D V : Type*}
    [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    (site : V → ℤ) (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (center : ℕ → ℤ → ℝ) (L K : ℝ)
    (extra : ℕ → ℤ → Prop) (keep : ℤ → Prop) (c : ℤ) :
    shiftMatrix (fun x : D × V => (x.1, site x.2)) (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate (fun t n =>
        maskedSignedIntegerWeight Q u eligible g center L K extra h keep t (n + c))) =
      blockNonbacktrackingMatrix (fun d i j =>
        if gate d (site i) (site j) ∧ keep (site i + c) ∧ keep (site j + c) then
          integerEdgeMatrix (fun i => site i + c) Q u (eligible (tuple d)) g (center (tuple d))
            L K (extra (tuple d)) h (tuple d) i j else 0) := by
  rw [physicalShiftMatrix_translate, physicalShiftWeight_masked_eq_integer]
  have hb := block_integer_matrix_eq_shift (fun i => site i + c) Q tuple u
    (fun d => eligible (tuple d)) g (fun d => center (tuple d)) L K
    (fun d => extra (tuple d)) h (integerVertexGate (fun d n m => gate d (n - c) (m - c)) keep)
  apply hb.symm.trans
  congr 1
  funext d i j
  simp only [integerVertexGate, add_sub_cancel_right]

end TwoPointCorrelations

end OAI
