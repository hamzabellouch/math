import OAI.Combinatorics.BinaryEdit.Model
import OAI.Combinatorics.TreeEdit.EditMetric

namespace OAI

namespace TreeEdit.BinaryLower

universe u
variable {α : Type u}

namespace EditStep

theorem length_le {x y : List α} (h : EditStep x y) : x.length ≤ y.length + 1 := by
  cases h <;> simp only [List.length_append, List.length_cons] <;> omega


end EditStep

namespace EditScript

theorem length_le {x y : List α} {n : ℕ} (h : EditScript x y n) :
    x.length ≤ y.length + n := by
  induction h with
  | nil x => simp
  | cons hxy hyz ih => have := EditStep.length_le hxy; omega

/-- Replace corresponding symbols, then insert or delete the leftover tail.
This uses at most the larger word length, including the empty-word cases. -/
theorem replace_all (x y : List α) :
    EditScript x y (max x.length y.length) := by
  induction x generalizing y with
  | nil => simpa using (TreeEdit.EditScript.erase y).symm
  | cons a x ih =>
    cases y with
    | nil => simpa using TreeEdit.EditScript.erase (a :: x)
    | cons b y =>
      have h : EditStep (a :: x) (b :: x) := by
        simpa using EditStep.substitute [] x a b
      simpa only [List.length_cons, max_add_add_right] using
        EditScript.cons h (by simpa using (ih y).append_left [b])


end EditScript

theorem length_le_length_add_editDistance (x y : List α) : x.length ≤ y.length + ed x y :=
  EditScript.length_le (ed_script x y)

/-- Positivity of ordinary edit distance does not require an inhabited alphabet. -/
theorem editDistance_pos_iff {x y : List α} : 0 < ed x y ↔ x ≠ y := by
  rw [Nat.pos_iff_ne_zero, ne_eq, ed_eq_zero_iff]

theorem editDistance_le_max_length (x y : List α) :
    ed x y ≤ max x.length y.length := ed_le_of_script (EditScript.replace_all x y)

@[simp] theorem editDistance_nil_right (x : List α) : ed x [] = x.length := by
  apply Nat.le_antisymm
  · exact ed_le_of_script (EditScript.erase x)
  · simpa using length_le_length_add_editDistance x []

@[simp] theorem editDistance_nil_left (x : List α) : ed [] x = x.length := by
  rw [ed_comm, editDistance_nil_right]

/-- Genuine changes only: this excludes the harmless identity substitutions
permitted by `EditStep`.  -/
inductive StrictEditScript : List α → List α → ℕ → Prop
  | nil (x : List α) : StrictEditScript x x 0
  | cons {x y z : List α} {n : ℕ} :
      EditStep x y → x ≠ y → StrictEditScript y z n → StrictEditScript x z (n + 1)

namespace StrictEditScript

theorem toScript {x y : List α} {n : ℕ} (h : StrictEditScript x y n) :
    EditScript x y n := by
  induction h with
  | nil x => exact .nil x
  | cons hxy hne hyz ih => exact .cons hxy ih

end StrictEditScript

/-- A minimum script never needs a redundant same-symbol substitution. -/
theorem EditScript.strict_of_optimal {x y : List α} {n : ℕ}
    (h : EditScript x y n) (hmin : ed x y = n) : StrictEditScript x y n := by
  induction h with
  | nil x => exact .nil x
  | @cons x y z n hxy hyz ih =>
    have htail : ed y z ≤ n := ed_le_of_script hyz
    have hshort : ed x z ≤ ed y z + 1 :=
      ed_le_of_script (.cons hxy (ed_script y z))
    have htailEq : ed y z = n := by omega
    have hne : x ≠ y := by
      intro heq
      subst y
      omega
    exact .cons hxy hne (ih htailEq)

theorem exists_optimal_strict_script (x y : List α) :
    StrictEditScript x y (ed x y) :=
  EditScript.strict_of_optimal (ed_script x y) rfl

/-- Thus the concrete definition is unchanged if substitutions are required
to change their symbol, exactly as in the ordinary edit convention. -/
theorem editDistance_eq_strict_minimum (x y : List α) :
    ed x y = sInf {n : ℕ | StrictEditScript x y n} := by
  apply Nat.le_antisymm
  · apply le_csInf
    · exact ⟨ed x y, exists_optimal_strict_script x y⟩
    · intro n hn
      exact ed_le_of_script hn.toScript
  · exact csInf_le (OrderBot.bddBelow _) (exists_optimal_strict_script x y)


end TreeEdit.BinaryLower

end OAI
