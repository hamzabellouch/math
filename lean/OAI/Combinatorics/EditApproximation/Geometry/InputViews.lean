import OAI.Combinatorics.EditApproximation.Geometry.Geometry

namespace OAI

/-! Input intervals are views into the stored arrays. Their semantic lists
are used by correctness statements; constructing a view stores only its
two endpoints and does not materialize that list. -/

namespace EditApproximation

structure InputView {α : Type*} (input : Array α) where
  lo : ℕ
  hi : ℕ
  ordered : lo ≤ hi
  valid : hi ≤ input.size

namespace InputView

variable {α : Type*} {input : Array α}

def width (view : InputView input) : ℕ := view.hi - view.lo

def contents (view : InputView input) : List α := substring input.toList view.lo view.hi

theorem contents_length (view : InputView input) : view.contents.length = view.width :=
  substring_length input.toList view.lo view.hi (by simpa only [Array.length_toList] using view.valid)

def get (view : InputView input) (i : Fin view.width) : α :=
  input[view.lo + i.val]'(by have h := i.isLt; have hv := view.valid; dsimp only [width] at h; omega)

theorem get_contents (view : InputView input) (i : Fin view.width) :
    view.get i = view.contents[i.val]'(by rw [contents_length]; exact i.isLt) := by
  simp only [get, contents, substring, List.getElem_drop, List.getElem_take, Array.getElem_toList]

def whole (input : Array α) : InputView input := ⟨0, input.size, Nat.zero_le _, le_rfl⟩

theorem whole_contents (input : Array α) : (whole input).contents = input.toList := by
  change (input.toList.take input.size).drop 0 = input.toList
  rw [List.drop_zero, List.take_of_length_le (by simp only [Array.length_toList, le_refl])]

def subview (view : InputView input) (lo hi : ℕ) (horder : lo ≤ hi) (hhi : hi ≤ view.width) :
    InputView input :=
  ⟨view.lo + lo, view.lo + hi, Nat.add_le_add_left horder _, by
    have hv := view.valid
    have ho := view.ordered
    dsimp only [width] at hhi
    omega⟩

theorem subview_width (view : InputView input) (lo hi : ℕ)
    (horder : lo ≤ hi) (hhi : hi ≤ view.width) :
    (view.subview lo hi horder hhi).width = hi - lo := by
  simp only [subview, width, Nat.add_sub_add_left]

/-- Reading a singleton view touches one stored array entry. -/
def head? (view : InputView input) : Option α :=
  if h : 0 < view.width then some (view.get ⟨0, h⟩) else none

theorem head?_contents (view : InputView input) : view.head? = view.contents.head? := by
  by_cases h : 0 < view.width
  · rw [head?, dite_eq_left h]
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [contents_length]; exact h)]
    exact congrArg some (get_contents view ⟨0, h⟩)
  · have hempty : view.contents = [] := List.length_eq_zero_iff.mp (by rw [contents_length]; omega)
    rw [head?, dite_eq_right h, hempty]
    rfl

end InputView

end EditApproximation

end OAI
