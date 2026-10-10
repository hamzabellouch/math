import OAI.Combinatorics.BinaryEdit.Model
import OAI.Combinatorics.TreeEdit.EditMetric

namespace OAI

namespace TreeEdit.BinaryLower

universe u v

/-- The real-valued form of the upper estimate used in `thm:804`. -/
theorem encode_editDistance_le_real {α : Type u} {β : Type v} {P : ℕ}
    (c : α → Word β P) (x y : List α) :
    (ed (encode c x) (encode c y) : ℝ) ≤
      (P : ℝ) * (ed x y : ℝ) := by
  exact_mod_cast ed_encode_le c x y

/-- Width `M²` and input length `M` give output length exactly `M³`. -/
theorem length_encode_cube {α : Type u} {β : Type v} {M : ℕ}
    (c : α → Word β (M ^ 2)) (x : Word α M) :
    (encode c x.val).length = M ^ 3 := by
  rw [length_encode, x.property]
  ring

end TreeEdit.BinaryLower

end OAI
