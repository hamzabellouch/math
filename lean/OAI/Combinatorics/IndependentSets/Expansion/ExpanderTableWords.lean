import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.Target
import OAI.Combinatorics.IndependentSets.Expansion.ExpanderTables

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open IndependentSetsGames.Foundations.Complexity (encodeWords decodeWords)

variable {v d : ℕ}

def rotationWords (table : Table v d) : List Nat := table.rows.toList.map Fin.val

@[simp] theorem rotationWords_length (table : Table v d) :
    (rotationWords table).length = v * d := by
  simp [rotationWords]

theorem rotationWords_getElem (table : Table v d) (i : ℕ) (hi : i < v * d) :
    (rotationWords table)[i]'(by simpa only [rotationWords_length] using hi) =
      (reverseIndex table ⟨i, hi⟩).val := by
  simp only [rotationWords, List.getElem_map, Vector.getElem_toList,
    reverseIndex, Fin.getElem_fin]

theorem rotationWords_get (table : Table v d) (i : Fin (v * d)) :
    (rotationWords table).get
      ⟨i.val, by simpa only [rotationWords_length] using i.isLt⟩ =
      (reverseIndex table i).val := by
  simpa only [List.get_eq_getElem] using rotationWords_getElem table i.val i.isLt

theorem rotationWords_getElem? (table : Table v d) (i : Fin (v * d)) :
    (rotationWords table)[i.val]? = some (reverseIndex table i).val := by
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨by simpa only [rotationWords_length] using i.isLt,
    rotationWords_getElem table i.val i.isLt⟩

theorem rotationWords_getElem?_none (table : Table v d) (i : ℕ) (hi : v * d ≤ i) :
    (rotationWords table)[i]? = none :=
  List.getElem?_eq_none (by simpa only [rotationWords_length] using hi)

theorem rotationWords_entry_lt (table : Table v d) (n : ℕ)
    (hn : n ∈ rotationWords table) : n < v * d := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
  exact a.isLt

theorem rotationWords_lookup (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[(rowIndex v d x).val]? =
      some (rowIndex v d (lookup table x)).val := by
  simpa only [lookup, Equiv.apply_symm_apply] using
    rotationWords_getElem? table (rowIndex v d x)

theorem rotationWords_row_order (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[x.2.val + d * x.1.val]? =
      some ((lookup table x).2.val + d * (lookup table x).1.val) := by
  simpa only [rowIndex_val] using rotationWords_lookup table x

@[simp] theorem decode_rotationWords (table : Table v d) :
    decodeWords (encodeWords (rotationWords table)) = some (rotationWords table) :=
  Complexity.decodeWords_encodeWords _

theorem decoded_lookup (table : Table v d) (i : Fin (v * d)) :
    (decodeWords (encodeWords (rotationWords table))).bind (fun words => words[i.val]?) =
      some (reverseIndex table i).val := by
  rw [decode_rotationWords]
  exact rotationWords_getElem? table i

theorem decoded_coordinate_lookup (table : Table v d) (x : Fin v × Fin d) :
    (decodeWords (encodeWords (rotationWords table))).bind
        (fun words => words[x.2.val + d * x.1.val]?) =
      some ((lookup table x).2.val + d * (lookup table x).1.val) := by
  rw [decode_rotationWords]
  exact rotationWords_row_order table x

theorem encode_rotationWords_length_eq (table : Table v d) :
    (encodeWords (rotationWords table)).length = (rotationWords table).sum + v * d := by
  rw [Complexity.encodeWords_length, rotationWords_length]

theorem encode_rotationWords_length_le (table : Table v d) :
    (encodeWords (rotationWords table)).length ≤ (v * d) * (v * d + 1) := by
  calc
    _ ≤ (rotationWords table).length * (v * d + 1) :=
      Complexity.encodeWords_length_le _ _
        (fun n hn => (rotationWords_entry_lt table n hn).le)
    _ = _ := by rw [rotationWords_length]

end IndependentSetsGames.Foundations.PCP.ExpanderTableWords

end OAI
