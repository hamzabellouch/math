import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_0 : Finset Cell := ⟨(([(1, 0), (2, 0), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_0 : Finset Cell := ⟨(([(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
theorem row_works_0 : Template HasSnaky 1 required_0 envelope_0 := by
  have hA : required_0 = snaky.erase (0, 0) := by decide +kernel
  have hT : envelope_0 = snaky := by decide +kernel
  rw [hA, hT]
  exact immediate_template HasSnaky snaky (0, 0) (by decide +kernel) identity_target
def required_1 : Finset Cell := ⟨(([(0, 0), (2, 0), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_1 : Finset Cell := ⟨(([(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
theorem row_works_1 : Template HasSnaky 1 required_1 envelope_1 := by
  have hA : required_1 = snaky.erase (1, 0) := by decide +kernel
  have hT : envelope_1 = snaky := by decide +kernel
  rw [hA, hT]
  exact immediate_template HasSnaky snaky (1, 0) (by decide +kernel) identity_target
def required_2 : Finset Cell := ⟨(([(0, 0), (1, 0), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_2 : Finset Cell := ⟨(([(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
theorem row_works_2 : Template HasSnaky 1 required_2 envelope_2 := by
  have hA : required_2 = snaky.erase (2, 0) := by decide +kernel
  have hT : envelope_2 = snaky := by decide +kernel
  rw [hA, hT]
  exact immediate_template HasSnaky snaky (2, 0) (by decide +kernel) identity_target
def required_3 : Finset Cell := ⟨(([(0, 0), (1, 0), (2, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_3 : Finset Cell := ⟨(([(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
theorem row_works_3 : Template HasSnaky 1 required_3 envelope_3 := by
  have hA : required_3 = snaky.erase (3, 0) := by decide +kernel
  have hT : envelope_3 = snaky := by decide +kernel
  rw [hA, hT]
  exact immediate_template HasSnaky snaky (3, 0) (by decide +kernel) identity_target
def required_4 : Finset Cell := ⟨(([(0, 0), (1, 0), (2, 0), (3, 0), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_4 : Finset Cell := ⟨(([(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
theorem row_works_4 : Template HasSnaky 1 required_4 envelope_4 := by
  have hA : required_4 = snaky.erase (3, 1) := by decide +kernel
  have hT : envelope_4 = snaky := by decide +kernel
  rw [hA, hT]
  exact immediate_template HasSnaky snaky (3, 1) (by decide +kernel) identity_target
def required_5 : Finset Cell := ⟨(([(0, 0), (1, 0), (2, 0), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_5 : Finset Cell := ⟨(([(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
theorem row_works_5 : Template HasSnaky 1 required_5 envelope_5 := by
  have hA : required_5 = snaky.erase (4, 1) := by decide +kernel
  have hT : envelope_5 = snaky := by decide +kernel
  rw [hA, hT]
  exact immediate_template HasSnaky snaky (4, 1) (by decide +kernel) identity_target
def height_0 : ℕ := 1
theorem base_required_exact_0 : required_0 = snaky.erase (0, 0) := by decide +kernel
theorem base_envelope_exact_0 : envelope_0 = snaky := by decide +kernel
theorem base_height_exact_0 : height_0 = 1 := rfl
def checked_0 : CheckedCard where
  required := required_0
  envelope := envelope_0
  height := height_0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_0
def height_1 : ℕ := 1
theorem base_required_exact_1 : required_1 = snaky.erase (1, 0) := by decide +kernel
theorem base_envelope_exact_1 : envelope_1 = snaky := by decide +kernel
theorem base_height_exact_1 : height_1 = 1 := rfl
def checked_1 : CheckedCard where
  required := required_1
  envelope := envelope_1
  height := height_1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_1
def height_2 : ℕ := 1
theorem base_required_exact_2 : required_2 = snaky.erase (2, 0) := by decide +kernel
theorem base_envelope_exact_2 : envelope_2 = snaky := by decide +kernel
theorem base_height_exact_2 : height_2 = 1 := rfl
def checked_2 : CheckedCard where
  required := required_2
  envelope := envelope_2
  height := height_2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_2
def height_3 : ℕ := 1
theorem base_required_exact_3 : required_3 = snaky.erase (3, 0) := by decide +kernel
theorem base_envelope_exact_3 : envelope_3 = snaky := by decide +kernel
theorem base_height_exact_3 : height_3 = 1 := rfl
def checked_3 : CheckedCard where
  required := required_3
  envelope := envelope_3
  height := height_3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_3
def height_4 : ℕ := 1
theorem base_required_exact_4 : required_4 = snaky.erase (3, 1) := by decide +kernel
theorem base_envelope_exact_4 : envelope_4 = snaky := by decide +kernel
theorem base_height_exact_4 : height_4 = 1 := rfl
def checked_4 : CheckedCard where
  required := required_4
  envelope := envelope_4
  height := height_4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_4
def height_5 : ℕ := 1
theorem base_required_exact_5 : required_5 = snaky.erase (4, 1) := by decide +kernel
theorem base_envelope_exact_5 : envelope_5 = snaky := by decide +kernel
theorem base_height_exact_5 : height_5 = 1 := rfl
def checked_5 : CheckedCard where
  required := required_5
  envelope := envelope_5
  height := height_5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_5
end SnakyPrototype.Certificate21

end OAI
