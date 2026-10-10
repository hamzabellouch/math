import OAI.Analysis.MetricEntropy.FieldGraphSeparation
import OAI.Analysis.MetricEntropy.GraphProfile
import OAI.Analysis.MetricEntropy.FormDimension

namespace OAI

/-!
# The finite-field graph matrix

The rows are literal symmetric forms, the labels are their actual contractions,
and every admissible set is included as a column index. The only input to the
separation theorem is the repeated-tuple nonvanishing conclusion constructed
by the robust-directions argument; graph separation is proved from it.
-/

noncomputable section

namespace MetricEntropyDuality.FiniteFieldRows

/-- All admissible subsets are fixed before a pair of rows is chosen. -/
def admissibleSets (θ : ℝ) (u : ℕ) : Finset (Finset (Fin u)) := by
  classical
  exact Finset.univ.filter (fun T => ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ))

@[simp] theorem mem_admissibleSets {θ : ℝ} {u : ℕ} {T : Finset (Fin u)} :
    T ∈ admissibleSets θ u ↔ ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) := by
  classical
  simp [admissibleSets]

theorem full_mem_admissibleSets {θ : ℝ} (hθ : 0 ≤ θ) (u : ℕ) :
    Finset.univ ∈ admissibleSets θ u := by
  apply mem_admissibleSets.mpr
  simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
  exact mul_nonneg hθ (Nat.cast_nonneg u)

theorem admissibleSets_nonempty {θ : ℝ} (hθ : 0 ≤ θ) (u : ℕ) :
    (admissibleSets θ u).Nonempty := ⟨Finset.univ, full_mem_admissibleSets hθ u⟩

abbrev RowIndex (p r h : ℕ) := SymmetricForm (ZMod p) r h

abbrev ColumnIndex (θ : ℝ) (p r h u : ℕ) :=
  GraphProfile.Columns (RowIndex p r h) (admissibleSets θ u)

/-- The literal contraction partition maps on forms of positive degree. -/
abbrev labels {p r j u : ℕ} (t : Fin u → (Fin r → ZMod p)) :=
  FieldGraphSeparation.labels (j := j) t

/-- The actual matrix, in the column-first convention of compression. -/
def column {p r j u : ℕ} (θ : ℝ) (t : Fin u → (Fin r → ZMod p)) :
    ColumnIndex θ p r (j + 1) u → RowIndex p r (j + 1) → ℝ :=
  GraphProfile.column (labels t) (admissibleSets θ u) (j + 1)

def row {p r j u : ℕ} (θ : ℝ) (t : Fin u → (Fin r → ZMod p))
    (x : RowIndex p r (j + 1)) : ColumnIndex θ p r (j + 1) u → ℝ :=
  GraphProfile.row (labels t) (admissibleSets θ u) (j + 1) x

theorem card_rowIndex (p r h : ℕ) [NeZero p] :
    Fintype.card (RowIndex p r h) = p ^ formDimension r h :=
  card_form_coefficients p r h

/-- The label range is counted in the actual space of lower-degree forms;
surjectivity of contraction is not needed. -/
theorem card_label_image_le {p r j u : ℕ} [NeZero p]
    (t : Fin u → (Fin r → ZMod p)) (i : Fin u) :
    (Finset.univ.image (labels (j := j) t i)).card ≤ p ^ formDimension r j := by
  classical
  calc
    _ ≤ Fintype.card (SymmetricForm (ZMod p) r j) := Finset.card_le_univ _
    _ = _ := card_form_coefficients p r j

/-- Including the full index set gives at least one column per row. -/
theorem card_rowIndex_le_columns {θ : ℝ} (hθ : 0 ≤ θ)
    (p r h u : ℕ) [NeZero p] :
    Fintype.card (RowIndex p r h) ≤ Fintype.card (ColumnIndex θ p r h u) := by
  classical
  apply Fintype.card_le_of_injective
    (fun x : RowIndex p r h => (x, ⟨Finset.univ, full_mem_admissibleSets hθ u⟩))
  intro x z hxz
  exact congrArg Prod.fst hxz

theorem columnIndex_nonempty {θ : ℝ} (hθ : 0 ≤ θ) (p r h u : ℕ) :
    Nonempty (ColumnIndex θ p r h u) :=
  ⟨(0, ⟨Finset.univ, full_mem_admissibleSets hθ u⟩)⟩

section Separation

variable {p r j u : ℕ} [NeZero p] {θ : ℝ}
variable (t : Fin u → (Fin r → ZMod p))
variable (hrobust : ∀ Z : SymmetricForm (ZMod p) r (j + 1), Z ≠ 0 →
  ∃ T : Finset (Fin u), ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) ∧
    T.Nonempty ∧ ∀ a : Fin (j + 1) → Fin u, (∀ l, a l ∈ T) →
      Z.eval (fun l => t (a l)) ≠ 0)

include hrobust

omit [NeZero p] in
/-- Robust nonvanishing gives separation in one of the actual admissible graphs. -/
theorem graph_separation (x y : RowIndex p r (j + 1)) (hxy : x ≠ y) :
    ∃ T ∈ admissibleSets θ u,
      ((j + 1 : ℕ) : ℕ∞) < PartitionGraph.distance (labels t) T x y := by
  obtain ⟨T, hbound, hT, hnonzero⟩ := hrobust (y - x) (sub_ne_zero.mpr hxy.symm)
  exact ⟨T, mem_admissibleSets.mpr hbound,
    FieldGraphSeparation.distance_gt t T hT x y hnonzero⟩

omit [NeZero p] in
/-- This coordinate statement is the direct input to the convex-body argument. -/
theorem exists_column_abs_eq_one (x y : RowIndex p r (j + 1)) (hxy : x ≠ y) :
    ∃ c : ColumnIndex θ p r (j + 1) u,
      |column θ t c x - column θ t c y| = 1 :=
  GraphProfile.exists_column_abs_eq_one (labels t) (admissibleSets θ u)
    (Nat.succ_pos j) x y (graph_separation t hrobust x y hxy)

/-- The full row distance is exactly one. -/
theorem norm_row_sub_eq_one (x y : RowIndex p r (j + 1)) (hxy : x ≠ y) :
    ‖row θ t x - row θ t y‖ = 1 :=
  GraphProfile.norm_row_sub_eq_one (labels t) (admissibleSets θ u)
    (Nat.succ_pos j) x y (graph_separation t hrobust x y hxy)

end Separation
end MetricEntropyDuality.FiniteFieldRows

end

end OAI
