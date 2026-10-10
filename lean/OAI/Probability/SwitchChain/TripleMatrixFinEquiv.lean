import OAI.Probability.SwitchChain.TripleGraphEncoding
import OAI.Probability.SwitchChain.ForcedColumns

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleMatrixFinEquiv
open TripleInternalEncoding
attribute [local instance] Classical.propDecidable

variable {W : Type*} [Fintype W]

def margins (e : ℕ) (c : W → ℕ) : Option W → ℕ :=
  fun w => w.elim (columnSum e) c

def augmentedEquiv (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) :
    AugmentedMatrix W e d c ≃
      ForcedColumns.FullMargins (margins e c) (fun i => d i - rowOffset e) where
  toFun M := ⟨fun i w => ⟨M.matrix i w, by have := M.binary i w; omega⟩,
    M.rows, M.columns⟩
  invFun M :=
    { matrix := fun i w => (M.val i w : ℕ)
      binary := fun i w => by have := (M.val i w).isLt; omega
      columns := M.property.2
      rows := M.property.1 }
  left_inv M := by apply AugmentedMatrix.ext; rfl
  right_inv M := by apply Subtype.ext; rfl

@[simp] theorem augmentedEquiv_apply_val (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ)
    (M : AugmentedMatrix W e d c) (i : Fin 3) (w : Option W) :
    ((augmentedEquiv e d c M).val i w : ℕ) = M.matrix i w := rfl

theorem augmented_row_eq_iff (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ)
    (M N : AugmentedMatrix W e d c) (i : Fin 3) :
    (augmentedEquiv e d c M).val i = (augmentedEquiv e d c N).val i ↔
      M.matrix i = N.matrix i := by
  constructor
  · intro h
    funext w
    exact congrArg Fin.val (congrFun h w)
  · intro h
    funext w
    apply Fin.ext
    exact congrFun h w

def graphEquiv (O : SimpleGraph W) (e : ℕ) (he : e ≤ 3)
    (d : Fin 3 → ℕ) (c : W → ℕ) (hd : ∀ i, rowOffset e ≤ d i) :
    GraphTripleCell O e d c ≃
      ForcedColumns.FullMargins (margins e c) (fun i => d i - rowOffset e) :=
  (graphTripleMatrixEquiv O e he d c hd).trans (augmentedEquiv e d c)

theorem graph_row_eq_iff (O : SimpleGraph W) (e : ℕ) (he : e ≤ 3)
    (d : Fin 3 → ℕ) (c : W → ℕ) (hd : ∀ i, rowOffset e ≤ d i)
    (G H : GraphTripleCell O e d c) (i : Fin 3) :
    (graphEquiv O e he d c hd G).val i = (graphEquiv O e he d c hd H).val i ↔
      (graphToCell G).outside i = (graphToCell H).outside i := by
  change (augmentedEquiv e d c (encodeCell (graphToCell G))).val i =
    (augmentedEquiv e d c (encodeCell (graphToCell H))).val i ↔ _
  rw [augmented_row_eq_iff, encode_row_eq_iff]

theorem bounds_of_nonempty (O : SimpleGraph W) (e : ℕ)
    (d : Fin 3 → ℕ) (c : W → ℕ) (h : Nonempty (GraphTripleCell O e d c)) :
    e ≤ 3 ∧ ∀ i, rowOffset e ≤ d i := by
  obtain ⟨G⟩ := h
  constructor
  · rw [← G.property.2.1]
    exact internalEdgeCount_le_three _
  · exact rowOffset_le_of_nonempty ⟨graphToCell G⟩

def graphEquivOfNonempty (O : SimpleGraph W) (e : ℕ)
    (d : Fin 3 → ℕ) (c : W → ℕ) (h : Nonempty (GraphTripleCell O e d c)) :
    GraphTripleCell O e d c ≃
      ForcedColumns.FullMargins (margins e c) (fun i => d i - rowOffset e) :=
  graphEquiv O e (bounds_of_nonempty O e d c h).1 d c
    (bounds_of_nonempty O e d c h).2

end Problem315.TripleMatrixFinEquiv

end

end OAI
