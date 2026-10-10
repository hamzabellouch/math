import OAI.NumberTheory.TwoPoint.Walks.RetainedRowScale

namespace OAI

/-! The explicit block-end, prefix-end, and exceptional-block errors
are exponentially small at the actual block length. -/

namespace TwoPointCorrelations

lemma retained_boundary_error_bound (L D h l M N : ℝ)
    (hL : 8 ≤ L) (hD0 : 0 ≤ D) (_hh0 : 0 ≤ h) (_hl0 : 0 ≤ l)
    (hD : D ≤ Real.exp (L / 4)) (hh : h ≤ Real.exp (L / 4))
    (hl : l ≤ Real.exp (L / 4))
    (hMlo : Real.exp (103 * L) ≤ M) (hMhi : M ≤ 2 * Real.exp (103 * L))
    (hN : Real.exp (106 * L) ≤ N) :
    l * D * Real.exp (-(2 * ⌊L⌋₊ : ℕ)) +
        (h * Real.exp (100 * L + 1)) / M * D + 2 * M / N * D ≤
      3 * Real.exp (-L) := by
  have hMp : 0 < M := (Real.exp_pos _).trans_le hMlo
  have hNp : 0 < N := (Real.exp_pos _).trans_le hN
  have hfloor := Nat.lt_floor_add_one L
  have htail : Real.exp (-(2 * ⌊L⌋₊ : ℕ)) ≤ Real.exp (-(3 * L / 2)) := by
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have hfirst : l * D * Real.exp (-(2 * ⌊L⌋₊ : ℕ)) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp (L / 4) * Real.exp (L / 4) * Real.exp (-(3 * L / 2)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hsecond : (h * Real.exp (100 * L + 1)) / M * D ≤ Real.exp (-L) := by
    calc
      _ ≤ (Real.exp (L / 4) * Real.exp (100 * L + 1)) /
          Real.exp (103 * L) * Real.exp (L / 4) := by gcongr
      _ = Real.exp (1 - 5 * L / 2) := by
        rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hfour : (4 : ℝ) ≤ Real.exp (L / 2) := by
    have hx := Real.add_one_le_exp (L / 2)
    linarith
  have hthird : 2 * M / N * D ≤ Real.exp (-L) := by
    calc
      _ ≤ 2 * (2 * Real.exp (103 * L)) / Real.exp (106 * L) * Real.exp (L / 4) := by gcongr
      _ = 4 * Real.exp (-11 * L / 4) := by
        rw [show 2 * (2 * Real.exp (103 * L)) = 4 * Real.exp (103 * L) by ring,
          mul_div_assoc, ← Real.exp_sub, mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      _ ≤ Real.exp (L / 2) * Real.exp (-11 * L / 4) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_pos _).le
      _ = Real.exp (-9 * L / 4) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  linarith

end TwoPointCorrelations

end OAI
