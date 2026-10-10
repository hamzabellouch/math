import Mathlib
import OAI.Computability.MaxCut.PCP.PortTables

namespace OAI

/-!
# Exact word offsets in executable port tables

These are optional list-lookup equalities for the unary-word stream consumed by
the lookup machine. They expose the stored tail, reverse index, and predicate
bit at their actual positions in the existing graph-table serialization.
-/

namespace MaxCutGames.Foundations.PCP.PortTableLookup

private theorem flatMap_word_inline_PortTableLookup {α β : Type*} (f : α → List β)
    (width j : Nat) (hj : j < width) :
    ∀ (rows : List α), (∀ a ∈ rows, (f a).length = width) →
      ∀ (i : Nat) (row : α), rows[i]? = some row →
        (rows.flatMap f)[width * i + j]? = (f row)[j]? := by
  intro rows
  induction rows with
  | nil =>
      intro _ i row selected
      simp at selected
  | cons a rows ih =>
      intro hwidth i row selected
      have ha : (f a).length = width := hwidth a (by simp)
      cases i with
      | zero =>
          have heq : a = row := by simpa using selected
          subst row
          simp only [Nat.mul_zero, Nat.zero_add, List.flatMap_cons]
          exact List.getElem?_append_left (by omega)
      | succ i =>
          have selected' : rows[i]? = some row := by simpa using selected
          have hskip : (f a).length ≤ width * (i + 1) + j := by
            rw [ha, Nat.mul_add, Nat.mul_one]
            omega
          have hoff : width * (i + 1) + j - (f a).length = width * i + j := by
            rw [ha, Nat.mul_add, Nat.mul_one]
            omega
          rw [List.flatMap_cons, List.getElem?_append_right hskip, hoff]
          exact ih (fun b hb => hwidth b (by simp [hb])) i row selected'

variable {n d : Nat}

/-- The first header word is the number of vertices. -/
theorem vertices_word (table : PortTables.Table n d) :
    (PortTables.tableWords table)[0]? = some n := rfl

/-- The second header word is the number of directed port occurrences. -/
theorem darts_word (table : PortTables.Table n d) :
    (PortTables.tableWords table)[1]? = some (n * d) := rfl

private theorem row_word_inline_PortTableLookup (table : PortTables.Table n d) (i : Fin (n * d))
    (j : Nat) (hj : j < 4098) :
    (PortTables.tableWords table)[2 + 4098 * i.val + j]? =
      (GraphTables.rowWords (PortTables.flatRows table)[i])[j]? := by
  rw [PortTables.tableWords_eq]
  change (n :: n * d :: (PortTables.flatRows table).toList.flatMap
    GraphTables.rowWords)[2 + 4098 * i.val + j]? = _
  rw [show 2 + 4098 * i.val + j = (4098 * i.val + j + 1) + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_cons_succ]
  apply flatMap_word_inline_PortTableLookup GraphTables.rowWords 4098 j hj
    (PortTables.flatRows table).toList
    (fun row _ => GraphTables.rowWords_length row) i.val
    ((PortTables.flatRows table)[i])
  simp only [Vector.getElem?_toList, Vector.getElem?_eq_getElem i.isLt,
    Fin.getElem_fin]

/-- The first word of row `i` records the tail vertex. -/
theorem tail_word (table : PortTables.Table n d) (i : Fin (n * d)) :
    (PortTables.tableWords table)[2 + 4098 * i.val]? =
      some (((PortTables.rowIndex n d).symm i).1.val) := by
  have h := row_word_inline_PortTableLookup table i 0 (by decide)
  simpa only [Nat.add_zero, GraphTables.rowWords, PortTables.flatRows,
    Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, List.cons_append,
    List.nil_append, List.getElem?_cons_zero] using h

/-- The second word of row `i` is the actual stored reverse index. -/
theorem reverse_word (table : PortTables.Table n d) (i : Fin (n * d)) :
    (PortTables.tableWords table)[3 + 4098 * i.val]? =
      some (table.reverseIndex[i].val) := by
  have h := row_word_inline_PortTableLookup table i 1 (by decide)
  rw [show 2 + 4098 * i.val + 1 = 3 + 4098 * i.val by omega] at h
  simpa only [GraphTables.rowWords, PortTables.flatRows, Fin.getElem_fin,
    Vector.getElem_ofFn, Fin.eta, List.cons_append, List.nil_append,
    List.getElem?_cons_succ, List.getElem?_cons_zero] using h

/-- Relation position `j` is a stored Boolean, encoded as its zero-or-one word. -/
theorem relation_word (table : PortTables.Table n d) (i : Fin (n * d))
    (j : Fin 4096) :
    (PortTables.tableWords table)[4 + 4098 * i.val + j.val]? =
      some (GraphTables.bitWord table.relations[i][j]) := by
  have h := row_word_inline_PortTableLookup table i (j.val + 2) (by omega)
  rw [show 2 + 4098 * i.val + (j.val + 2) = 4 + 4098 * i.val + j.val by omega] at h
  simpa only [GraphTables.rowWords, GraphTables.relationWords,
    PortTables.flatRows, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    List.cons_append, List.nil_append, List.getElem?_cons_succ,
    List.getElem?_map, Vector.getElem?_toList,
    Vector.getElem?_eq_getElem j.isLt, Option.map_some] using h

/-- A lookup indexed by the two labels returns exactly the semantic predicate. -/
theorem accepts_word (table : PortTables.Table n d) (e : Fin n × Fin d)
    (a b : PortTables.Label) :
    (PortTables.tableWords table)[4 + 4098 * (PortTables.rowIndex n d e).val +
        (GraphTables.relationIndex (a, b)).val]? =
      some (GraphTables.bitWord (PortTables.accepts table e a b)) :=
  relation_word table (PortTables.rowIndex n d e) (GraphTables.relationIndex (a, b))

/-- After the reverse-index lookup, the target row's tail is the rotor endpoint. -/
theorem rotation_head_word (table : PortTables.Table n d) (e : Fin n × Fin d) :
    (PortTables.tableWords table)[2 + 4098 * (table.reverseIndex[PortTables.rowIndex n d e]).val]? =
      some ((PortTables.rotation table e).1.val) :=
  tail_word table (table.reverseIndex[PortTables.rowIndex n d e])

/-- Both selections required by a concrete two-lookup rotor implementation. -/
theorem rotor_lookups (table : PortTables.Table n d) (e : Fin n × Fin d) :
    (PortTables.tableWords table)[3 + 4098 * (PortTables.rowIndex n d e).val]? =
      some (table.reverseIndex[PortTables.rowIndex n d e].val) ∧
    (PortTables.tableWords table)[2 + 4098 * (table.reverseIndex[PortTables.rowIndex n d e]).val]? =
      some ((PortTables.rotation table e).1.val) :=
  ⟨reverse_word table (PortTables.rowIndex n d e), rotation_head_word table e⟩

end MaxCutGames.Foundations.PCP.PortTableLookup

end OAI
