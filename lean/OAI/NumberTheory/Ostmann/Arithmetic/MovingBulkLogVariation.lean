import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkLogWeight

namespace OAI

/-! # Variation of the retained logarithmic bulk weights -/

namespace Ostmann
open scoped Classical

/-- Freezing each prime in a log cell of diameter `η` changes the retained
bulk cutoff by at most its number of slots times one fixed Lipschitz constant. -/
theorem movingBulkListLogWeight_variation {σ : Type*}
    (value value' : σ → ℕ) (outside : List ℕ) (cb cd D η : ℝ)
    (hD : 0 ≤ D)
    (hprofile : ∀ x y, |logCellProfile x - logCellProfile y| ≤ D * |x - y|)
    (bulk : List σ)
    (hclose : ∀ a ∈ bulk, |Real.log (value a : ℝ) - Real.log (value' a : ℝ)| ≤ η) :
    |movingBulkListLogWeight value outside cb cd bulk -
        movingBulkListLogWeight value' outside cb cd bulk| ≤ D * bulk.length * η := by
  have hs : |(bulk.map (fun a => Real.log (value a : ℝ))).sum -
      (bulk.map (fun a => Real.log (value' a : ℝ))).sum| ≤ (bulk.length : ℝ) * η := by
    induction bulk with
    | nil => simp
    | cons a bulk ih =>
      have ha := hclose a List.mem_cons_self
      have hb := ih (fun b hb => hclose b (List.mem_cons_of_mem a hb))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        _ = |(Real.log (value a : ℝ) - Real.log (value' a : ℝ)) +
            ((bulk.map (fun b => Real.log (value b : ℝ))).sum -
              (bulk.map (fun b => Real.log (value' b : ℝ))).sum)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ η + (bulk.length : ℝ) * η := add_le_add ha hb
        _ = _ := by ring
  unfold movingBulkListLogWeight
  rw [← sub_mul, abs_mul, abs_of_nonneg (logCellProfile_nonneg _)]
  have hl := hprofile
    ((bulk.map (fun a => Real.log (value a : ℝ))).sum - cb)
    ((bulk.map (fun a => Real.log (value' a : ℝ))).sum - cb)
  have hsub :
      (bulk.map (fun a => Real.log (value a : ℝ))).sum - cb -
        ((bulk.map (fun a => Real.log (value' a : ℝ))).sum - cb) =
      (bulk.map (fun a => Real.log (value a : ℝ))).sum -
        (bulk.map (fun a => Real.log (value' a : ℝ))).sum := by ring
  rw [hsub] at hl
  calc
    _ ≤ (D * |(bulk.map (fun a => Real.log (value a : ℝ))).sum -
        (bulk.map (fun a => Real.log (value' a : ℝ))).sum|) * 1 :=
      mul_le_mul hl (logCellProfile_le_one _) (logCellProfile_nonneg _)
        (mul_nonneg hD (abs_nonneg _))
    _ ≤ D * ((bulk.length : ℝ) * η) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left hs hD
    _ = _ := by ring

end Ostmann

end OAI
