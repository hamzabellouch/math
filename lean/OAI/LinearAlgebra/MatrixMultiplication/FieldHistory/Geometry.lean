import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Transitions

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
attribute [local instance] Classical.propDecidable Classical.decEq

def currentShape {K : ℕ} : CanonicalHistory K → Shape
  | .initial h => initialShape h
  | .afterA h => aShape h
  | .afterB h => bShape h
  | .partC h => cShapeParent h
  | .afterC h => cShape h

def currentLength {K : ℕ} : CanonicalHistory K → ℕ
  | .initial _ => 8
  | .afterA _ => 4
  | .afterB _ | .partC _ => 2
  | .afterC _ => 1

def currentPhysicalShape {K : ℕ} (h : History K) : Shape :=
  physicalShape h.2 (currentShape h.1)

theorem currentShape_spec {K : ℕ} (h : CanonicalHistory K) :
    ShapeBounded (currentShape h) ∧ shapeTotal (currentShape h) = 2 * currentLength h := by
  cases h with
  | initial h => exact root_shape_spec _ (initialShape_mem h)
  | afterA h => exact ⟨mem_shapes_bounded (aShape_size h) (by omega), mem_shapes_total (aShape_size h)⟩
  | afterB h => exact ⟨mem_shapes_bounded (bShape_size h) (by omega), mem_shapes_total (bShape_size h)⟩
  | partC h => exact ⟨mem_shapes_bounded (bShape_size h.1.val) (by omega),
      mem_shapes_total (bShape_size h.1.val)⟩
  | afterC h =>
      cases hh : h.2.2 with
      | false =>
          simpa only [currentShape, currentLength, cShape, cSplit, cShapeParent,
            halfShape, hh, Bool.false_eq_true, ite_false, mul_one] using
            stageC_shape_spec _ (bShape_size h.1.1.val) h.1.1.property h.2.1
      | true =>
          simpa only [currentShape, currentLength, cShape, cSplit, cShapeParent,
            halfShape, hh, ite_true, mul_one] using
            stageC_complement_spec _ (bShape_size h.1.1.val) h.1.1.property h.2.1

theorem currentPhysicalShape_total {K : ℕ} (h : History K) :
    shapeTotal (currentPhysicalShape h) = 2 * currentLength h.1 :=
  (physicalShape_total h.2 _).trans (currentShape_spec h.1).2

theorem positive_iff_no_zero (u : Shape) : positive u = true ↔ ∀ i, u i ≠ 0 := by
  simp only [positive, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h i
    fin_cases i
    · change u 0 ≠ 0
      omega
    · change u 1 ≠ 0
      omega
    · change u 2 ≠ 0
      omega
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    omega

theorem not_positive_has_zero (u : Shape) (hu : positive u ≠ true) : ∃ i, u i = 0 := by
  by_contra hn
  apply hu
  rw [positive_iff_no_zero]
  intro i hi
  exact hn ⟨i, hi⟩

theorem terminal_has_zero {K : ℕ} (h : CanonicalHistory K) (ht : terminal h) :
    ∃ i, currentShape h i = 0 := by
  cases h with
  | initial h =>
      apply not_positive_has_zero
      intro hp
      exact ht (List.mem_filter.mpr ⟨initialShape_mem h, hp⟩)
  | afterA h =>
      apply not_positive_has_zero
      intro hp
      exact ht (List.mem_filter.mpr ⟨aShape_size h, hp⟩)
  | afterB h => exact not_positive_has_zero _ ht
  | partC h => exact False.elim ht
  | afterC h => exact cShape_zero h

theorem terminal_physical_zero {K : ℕ} (h : History K) (ht : terminal h.1) :
    ∃ s, currentPhysicalShape h s = 0 := by
  obtain ⟨i, hi⟩ := terminal_has_zero h.1 ht
  exact ⟨h.2 i, by simpa only [currentPhysicalShape, physicalShape_source] using hi⟩

theorem final_physical_zero {K : ℕ} (h : State K (K + 2)) :
    ∃ s, currentPhysicalShape h.val s = 0 :=
  terminal_physical_zero h.val (final_state_terminal h)

theorem source_shape {K : ℕ} (w : Work K) : currentShape w.source = w.parentShape := by
  cases w <;> rfl

theorem source_length {K : ℕ} (w : Work K) : currentLength w.source = 2 * w.halfLength := by
  cases w <;> rfl

theorem child_shape {K : ℕ} (w : Work K) (b : w.Branch) (right : Bool) :
    currentShape (w.child b right) = halfShape w.parentShape (w.splitShape b) right := by
  cases w <;> rfl

theorem child_length {K : ℕ} (w : Work K) (b : w.Branch) (right : Bool) :
    currentLength (w.child b right) = w.halfLength := by
  cases w <;> rfl

end MatrixMultiplication.AllFieldHistory

end

end OAI
