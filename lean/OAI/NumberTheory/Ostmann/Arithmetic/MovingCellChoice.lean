import OAI.NumberTheory.Ostmann.Arithmetic.MovingRoundedCellSums

namespace OAI

/-! # Integer cell centers outside a finite set of failures -/

namespace Ostmann
open scoped Classical

/-- At most `card D` failures move an integer center by at most `card D + 1`.
This one-sided choice also preserves every lower endpoint target. -/
theorem integer_cell_center_avoiding (D : Finset ℤ) (T : ℝ) :
    ∃ c : ℤ, c ∉ D ∧ T ≤ (c : ℝ) ∧ (c : ℝ) ≤ T + D.card + 1 := by
  let a : ℤ := ⌈T⌉
  let S := (Finset.range (D.card + 1)).image (fun j : ℕ => a + (j : ℤ))
  have hcard : S.card = D.card + 1 := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range _
    · intro i j hij
      exact_mod_cast (add_left_cancel hij : (i : ℤ) = (j : ℤ))
  have hex : ∃ c ∈ S, c ∉ D := by
    by_contra! h
    have hsub : S ⊆ D := h
    have hc := Finset.card_le_card hsub
    omega
  obtain ⟨c, hc, hnot⟩ := hex
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
  have hjR : (j : ℝ) ≤ D.card := by
    exact_mod_cast (show j ≤ D.card from Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  refine ⟨a + j, hnot, ?_, ?_⟩
  · push_cast
    exact (Int.le_ceil T).trans (le_add_of_nonneg_right (Nat.cast_nonneg j))
  · push_cast
    have ha : (a : ℝ) < T + 1 := Int.ceil_lt_add_one T
    linarith

theorem nat_cell_center_avoiding (D : Finset ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ c : ℕ, c ∉ D ∧ T ≤ (c : ℝ) ∧ (c : ℝ) ≤ T + D.card + 1 := by
  let a := ⌈T⌉₊
  let S := (Finset.range (D.card + 1)).image (fun j => a + j)
  have hcard : S.card = D.card + 1 := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range _
    · exact fun _ _ hij => Nat.add_left_cancel hij
  have hex : ∃ c ∈ S, c ∉ D := by
    by_contra! h
    have hc := Finset.card_le_card (show S ⊆ D from h)
    omega
  obtain ⟨c, hc, hnot⟩ := hex
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
  have hjR : (j : ℝ) ≤ D.card := by
    exact_mod_cast (show j ≤ D.card from Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  refine ⟨a + j, hnot, ?_, ?_⟩
  · push_cast
    exact (Nat.le_ceil T).trans (le_add_of_nonneg_right (Nat.cast_nonneg j))
  · push_cast
    have ha : (a : ℝ) < T + 1 := Nat.ceil_lt_add_one hT
    linarith

theorem compensation_cell_center_avoiding (D : Finset ℤ) (w : ℝ) :
    ∃ c : ℤ, c ∉ D ∧ w ≤ 4 * (c : ℝ) ∧
      4 * ((c : ℝ) + 1) ≤ w + 4 * (D.card + 2) := by
  obtain ⟨c, hc, hlo, hhi⟩ := integer_cell_center_avoiding D (w / 4)
  refine ⟨c, hc, ?_, ?_⟩ <;> linarith

/-- All six protected top slots may use one good cell; the resulting error
is upward and does not weaken the protected lower bound. -/
theorem protected_cell_center_avoiding (D : Finset ℤ) (J cb : ℝ) :
    ∃ c : ℤ, c ∉ D ∧ J ≤ 6 * (c : ℝ) + cb ∧
      6 * ((c : ℝ) + 1) + cb ≤ J + 6 * (D.card + 2) := by
  obtain ⟨c, hc, hlo, hhi⟩ := integer_cell_center_avoiding D ((J - cb) / 6)
  refine ⟨c, hc, ?_, ?_⟩ <;> linarith

end Ostmann

end OAI
