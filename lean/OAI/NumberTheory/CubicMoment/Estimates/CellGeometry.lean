import OAI.NumberTheory.CubicMoment.Estimates.CellBounds

namespace OAI

/-!
# Geometry of the product-boundary cells

After scaling log-norm by the cell width, the two norm cells are unit
intervals. A pair meeting a width-one strip around the product boundary
can lie on only five integer diagonals. This proves the bounded-neighbor
claim used in `eq:near-cell-diagonal` rather than postulating it.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

def nearCellOffsets (c : ℝ) : Finset ℤ := Finset.Icc (⌊c⌋ - 3) (⌊c⌋ + 1)

@[simp] theorem nearCellOffsets_card (c : ℝ) : (nearCellOffsets c).card = 5 := by
  simp only [nearCellOffsets, Int.card_Icc]
  omega

/-- A cell pair that meets the boundary strip has one of five index sums. -/
theorem nearCell_index_mem {i j : ℤ} {x y c : ℝ}
    (hx : (i : ℝ) ≤ x ∧ x ≤ (i : ℝ) + 1)
    (hy : (j : ℝ) ≤ y ∧ y ≤ (j : ℝ) + 1)
    (hnear : |x + y - c| ≤ 1) : i + j ∈ nearCellOffsets c := by
  rcases abs_le.mp hnear with ⟨hl, hu⟩
  have hf := Int.floor_le c
  have hf' := Int.lt_floor_add_one c
  have hlo : ((⌊c⌋ - 3 : ℤ) : ℝ) ≤ ((i + j : ℤ) : ℝ) := by
    push_cast
    linarith
  have hhi : ((i + j : ℤ) : ℝ) < ((⌊c⌋ + 2 : ℤ) : ℝ) := by
    push_cast
    linarith
  have hhi' : i + j < ⌊c⌋ + 2 := by exact_mod_cast hhi
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo, by omega⟩

theorem nearCell_row_degree (E : Finset (ℤ × ℤ)) (c : ℝ)
    (hE : ∀ e ∈ E, e.1 + e.2 ∈ nearCellOffsets c) (i : ℤ) :
    (E.filter (fun e => e.1 = i)).card ≤ 5 := by
  rw [← nearCellOffsets_card c]
  apply Finset.card_le_card_of_injOn (fun e : ℤ × ℤ => e.1 + e.2)
  · intro e he
    exact hE e (Finset.mem_filter.mp he).1
  · intro e he f hf hsum
    have he' := (Finset.mem_filter.mp he).2
    have hf' := (Finset.mem_filter.mp hf).2
    change e.1 + e.2 = f.1 + f.2 at hsum
    apply Prod.ext
    · exact he'.trans hf'.symm
    · omega

theorem nearCell_column_degree (E : Finset (ℤ × ℤ)) (c : ℝ)
    (hE : ∀ e ∈ E, e.1 + e.2 ∈ nearCellOffsets c) (j : ℤ) :
    (E.filter (fun e => e.2 = j)).card ≤ 5 := by
  rw [← nearCellOffsets_card c]
  apply Finset.card_le_card_of_injOn (fun e : ℤ × ℤ => e.1 + e.2)
  · intro e he
    exact hE e (Finset.mem_filter.mp he).1
  · intro e he f hf hsum
    have he' := (Finset.mem_filter.mp he).2
    have hf' := (Finset.mem_filter.mp hf).2
    change e.1 + e.2 = f.1 + f.2 at hsum
    apply Prod.ext
    · omega
    · exact he'.trans hf'.symm

/-- The product-boundary diagonal bound with an absolute constant. -/
theorem near_product_boundary_bound (I J : Finset ℤ) (E : Finset (ℤ × ℤ))
    (a b : ℤ → ℝ) (c : ℝ) (hI : ∀ e ∈ E, e.1 ∈ I) (hJ : ∀ e ∈ E, e.2 ∈ J)
    (hE : ∀ e ∈ E, ∃ x y : ℝ,
      (e.1 : ℝ) ≤ x ∧ x ≤ (e.1 : ℝ) + 1 ∧
      (e.2 : ℝ) ≤ y ∧ y ≤ (e.2 : ℝ) + 1 ∧ |x + y - c| ≤ 1) :
    (∑ e ∈ E, a e.1 * b e.2) ≤
      5 * Real.sqrt (∑ i ∈ I, (a i) ^ 2) * Real.sqrt (∑ j ∈ J, (b j) ^ 2) := by
  have hdiag : ∀ e ∈ E, e.1 + e.2 ∈ nearCellOffsets c := by
    intro e he
    obtain ⟨x, y, hxl, hxu, hyl, hyu, hn⟩ := hE e he
    exact nearCell_index_mem ⟨hxl, hxu⟩ ⟨hyl, hyu⟩ hn
  exact near_cell_sum_le I J E a b 5 hI hJ
    (fun i _ => nearCell_row_degree E c hdiag i)
    (fun j _ => nearCell_column_degree E c hdiag j)

end CubicFirstMoment

end

end OAI
