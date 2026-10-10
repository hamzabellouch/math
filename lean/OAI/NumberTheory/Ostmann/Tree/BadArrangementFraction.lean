import OAI.NumberTheory.Ostmann.Tree.BadArrangementCount
import OAI.NumberTheory.Ostmann.Construction.FactorialExponential

namespace OAI

/-! # The exponentially small proportion of bad bulk arrangements -/

namespace Ostmann

open scoped Classical

theorem badBulkArrangement_fraction_bound {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} : ℝ) /
        ((r * m).factorial : ℝ) ≤
      ((r + 1) * r ^ (2 * r) : ℕ) *
        Real.exp ((r : ℝ) * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4)) := by
  let C : ℝ := ((r + 1) * r ^ (2 * r) : ℕ)
  let q : ℝ := (m : ℝ) * r * (Real.log r + 1) / 4
  have hc := badBulkArrangement_count_bound hr (show 0 < m by omega)
  change (Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} : ℝ) ≤
    C * (m.factorial : ℝ) ^ r * Real.exp q at hc
  calc
    _ ≤ C * (m.factorial : ℝ) ^ r * Real.exp q / ((r * m).factorial : ℝ) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = (C * Real.exp q) * ((m.factorial : ℝ) ^ r / ((r * m).factorial : ℝ)) := by ring
    _ ≤ (C * Real.exp q) * Real.exp ((r : ℝ) * m * (1 - Real.log r)) :=
      mul_le_mul_of_nonneg_left (block_factorial_ratio hr hm) (by dsimp [C]; positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [q]
      ring

/-- The total number of labeled arrangements is (rm)!, including when
different slots happen to contain the same prime value. -/
theorem card_bulkPerm (r m : ℕ) :
    Fintype.card (Equiv.Perm (Fin r × Fin m)) = (r * m).factorial := by
  rw [Fintype.card_perm, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

end Ostmann

end OAI
