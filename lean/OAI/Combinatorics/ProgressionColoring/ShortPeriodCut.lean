import OAI.Combinatorics.ProgressionColoring.CyclicModel

namespace OAI

/-! A failed affine lift of centered circle representatives crosses the cut.

The crossing is allowed at either endpoint of the parameter interval. This is
needed when the initial centered representative is the included endpoint
`-1 / 2` and the affine line immediately leaves the centered interval.
-/

namespace QuantitativeVanDerWaerden

/-- Two centered representatives congruent modulo the integers are equal. -/
theorem centered_representative_unique_of_integer_difference {x y : ℝ}
    (hx : -(1 / 2 : ℝ) ≤ x ∧ x < 1 / 2)
    (hy : -(1 / 2 : ℝ) ≤ y ∧ y < 1 / 2)
    (hcongr : ∃ z : ℤ, x - y = z) : x = y := by
  obtain ⟨z, hz⟩ := hcongr
  have habs : |(z : ℝ)| < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hz0 : z = 0 := integer_eq_zero_of_abs_lt_one habs
  rw [hz0, Int.cast_zero] at hz
  linarith

/-- A real affine segment starting in the centered interval and ending
outside it meets one of the two boundary representatives of the circle cut. -/
theorem affine_cut_of_leaving_centered_interval {A w T : ℝ}
    (hA : -(1 / 2 : ℝ) ≤ A ∧ A < 1 / 2) (hT : 0 ≤ T)
    (hout : ¬ (-(1 / 2 : ℝ) ≤ A + T * w ∧ A + T * w < 1 / 2)) :
    w ≠ 0 ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧
      ∃ z : ℤ, A + t * w = 1 / 2 + z := by
  by_cases hlow : A + T * w < -(1 / 2 : ℝ)
  · have hw : w < 0 := by
      by_contra h
      have hp := mul_nonneg hT (le_of_not_gt h)
      linarith [hA.1]
    refine ⟨ne_of_lt hw, (-1 / 2 - A) / w, ?_, ?_, -1, ?_⟩
    · exact div_nonneg_of_nonpos (by linarith [hA.1]) hw.le
    · apply (div_le_iff_of_neg hw).mpr
      linarith
    · rw [div_mul_cancel₀ _ (ne_of_lt hw)]
      norm_num
  · have hu : (1 / 2 : ℝ) ≤ A + T * w := by
      by_contra h
      exact hout ⟨le_of_not_gt hlow, lt_of_not_ge h⟩
    have hw : 0 < w := by
      by_contra h
      have hp := mul_nonpos_of_nonneg_of_nonpos hT (le_of_not_gt h)
      linarith [hA.2]
    refine ⟨ne_of_gt hw, (1 / 2 - A) / w, ?_, ?_, 0, ?_⟩
    · exact div_nonneg (by linarith [hA.2]) hw.le
    · apply (div_le_iff₀ hw).mpr
      linarith
    · rw [div_mul_cancel₀ _ (ne_of_gt hw)]
      norm_num

/-- Failure of a real affine lift of a finite centered progression gives a
cut crossing at a real parameter between `0` and `k - 1`. Integer congruence
alone suffices; no assumption on the size of the affine step is needed. -/
theorem failed_centered_lift_cut {Y : ℕ → ℝ} {A w : ℝ} {k : ℕ}
    (hrep : ∀ j, j < k → -(1 / 2 : ℝ) ≤ Y j ∧ Y j < 1 / 2)
    (hbase : Y 0 = A)
    (hcongr : ∀ j, j < k → ∃ z : ℤ, Y j - (A + (j : ℝ) * w) = z)
    (hfail : ∃ j, j < k ∧ Y j ≠ A + (j : ℝ) * w) :
    w ≠ 0 ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ (k : ℝ) - 1 ∧
      ∃ z : ℤ, A + t * w = 1 / 2 + z := by
  obtain ⟨j, hj, hfail⟩ := hfail
  have hA : -(1 / 2 : ℝ) ≤ A ∧ A < 1 / 2 := by
    simpa only [hbase] using hrep 0 (by omega)
  have hout : ¬ (-(1 / 2 : ℝ) ≤ A + (j : ℝ) * w ∧
      A + (j : ℝ) * w < 1 / 2) := by
    intro hmem
    exact hfail (centered_representative_unique_of_integer_difference
      (hrep j hj) hmem (hcongr j hj))
  obtain ⟨hw, t, ht0, htj, z, hz⟩ :=
    affine_cut_of_leaving_centered_interval hA (Nat.cast_nonneg j) hout
  have hjk : (j : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast (show j + 1 ≤ k from hj)
  exact ⟨hw, t, ht0, by linarith, z, hz⟩

end QuantitativeVanDerWaerden

end OAI
