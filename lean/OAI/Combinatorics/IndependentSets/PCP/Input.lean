import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.GameEncoding
import OAI.Combinatorics.IndependentSets.PCP.ClauseVerifier
import OAI.Combinatorics.IndependentSets.PCP.GenericGraphTables

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Input

open IndependentSetsGames.Foundations.Complexity

export GenericGraphTables (Label RelationTable DartRow Rows Valid Table
  relationIndex relationIndex_val relationAt relationOf relationAt_relationOf
  reverseAt acceptsAt rowList rowList_length semantics semantics_reverse
  semantics_tail semantics_accepts ofGraph semantics_ofGraph ofEnumeratedGraph
  bitWord relationWords relationWords_length rowWords rowWords_length
  rowsWords_length tableWords tableWords_length tableBits encoding
  parseRelation parseRow parseRows decodeTableWords decodeTableBits
  parseRelation_encoded parseRow_encoded parseRows_encoded
  decodeTableWords_encoded decodeTableBits_encoded tableBits_injective
  relationBits_length_le rowBits_length_le rowsBits_length_le tableWords_length_le_bits
  tableBits_length_le vertices_le_tableBits_length darts_le_tableBits_length)

variable {q n m : Nat}

abbrev rowWidth (q : Nat) : Nat := q * q + 2

def rowOffset (q e : Nat) : Nat := 2 + rowWidth q * e

theorem rowsWords_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    rows.flatMap rowWords = (rows.take e).flatMap rowWords ++
      (rowWords rows[e] ++ (rows.drop (e + 1)).flatMap rowWords) := by
  have hs : rows.take e ++ rows[e] :: rows.drop (e + 1) = rows := by
    rw [List.getElem_cons_drop he, List.take_append_drop]
  have hw := congrArg (fun rs : List (DartRow q n m) => rs.flatMap rowWords) hs
  simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using hw.symm

theorem rowsBits_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    encodeWords (rows.flatMap rowWords) =
      encodeWords ((rows.take e).flatMap rowWords) ++
        (encodeWords (rowWords rows[e]) ++
          encodeWords ((rows.drop (e + 1)).flatMap rowWords)) := by
  rw [rowsWords_split rows e he]
  simp only [encodeWords_append]

theorem rowsBits_append_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) (suffix : List Bool) :
    encodeWords (rows.flatMap rowWords) ++ suffix =
      encodeWords ((rows.take e).flatMap rowWords) ++
        (encodeWords (rowWords rows[e]) ++
          (encodeWords ((rows.drop (e + 1)).flatMap rowWords) ++ suffix)) := by
  rw [rowsBits_split rows e he]
  simp only [List.append_assoc]

def prefixWords (table : Table q) (e : Fin table.darts) : List Nat :=
  [table.vertices, table.darts] ++ ((rowList table).take e.val).flatMap rowWords

def suffixWords (table : Table q) (e : Fin table.darts) : List Nat :=
  ((rowList table).drop (e.val + 1)).flatMap rowWords

theorem prefixWords_length (table : Table q) (e : Fin table.darts) :
    (prefixWords table e).length = rowOffset q e.val := by
  simp [prefixWords, rowOffset, rowWidth, Nat.mul_comm, Nat.add_comm]
  omega

theorem tableWords_at_row (table : Table q) (e : Fin table.darts) :
    tableWords table = prefixWords table e ++
      (rowWords table.rows[e] ++ suffixWords table e) := by
  have hs := rowsWords_split (rowList table) e.val (by simpa only [rowList_length] using e.isLt)
  simp only [rowList, Vector.getElem_toList] at hs
  unfold tableWords prefixWords suffixWords rowList
  rw [hs]
  simp only [List.append_assoc, Fin.getElem_fin]

theorem tableBits_at_row (table : Table q) (e : Fin table.darts) :
    tableBits table = encodeWords (prefixWords table e) ++
      (encodeWords (rowWords table.rows[e]) ++ encodeWords (suffixWords table e)) := by
  rw [tableBits, tableWords_at_row table e]
  simp only [encodeWords_append]

theorem tableBits_header (table : Table q) :
    tableBits table = encodeWord table.vertices ++
      (encodeWord table.darts ++ encodeWords ((rowList table).flatMap rowWords)) := by
  simp [tableBits, tableWords, encodeWords]

theorem tableWords_drop_row (table : Table q) (e : Fin table.darts) :
    (tableWords table).drop (rowOffset q e.val) =
      rowWords table.rows[e] ++ suffixWords table e := by
  rw [tableWords_at_row table e]
  exact List.drop_left' (l₂ := rowWords table.rows[e] ++ suffixWords table e)
    (prefixWords_length table e)

theorem tableWords_take_row (table : Table q) (e : Fin table.darts) :
    ((tableWords table).drop (rowOffset q e.val)).take (rowWidth q) =
      rowWords table.rows[e] := by
  rw [tableWords_drop_row]
  exact List.take_left' (l₂ := suffixWords table e) (rowWords_length table.rows[e])

theorem tableWords_get_tail (table : Table q) (e : Fin table.darts) :
    (tableWords table)[rowOffset q e.val]? = some table.rows[e].tail.val := by
  have h := congrArg (fun words : List Nat => words[0]?) (tableWords_drop_row table e)
  simpa [List.getElem?_drop, rowWords] using h

theorem tableWords_get_reverse (table : Table q) (e : Fin table.darts) :
    (tableWords table)[rowOffset q e.val + 1]? = some table.rows[e].reverseIndex.val := by
  have h := congrArg (fun words : List Nat => words[1]?) (tableWords_drop_row table e)
  simpa [List.getElem?_drop, rowWords] using h

theorem tableWords_drop_relation (table : Table q) (e : Fin table.darts) :
    (tableWords table).drop (rowOffset q e.val + 2) =
      relationWords table.rows[e].relation ++ suffixWords table e := by
  rw [← List.drop_drop, tableWords_drop_row]
  simp [rowWords]

theorem relationWords_get (relation : RelationTable q) (j : Fin (q * q)) :
    (relationWords relation)[j.val]? = some (bitWord relation[j]) := by
  rw [List.getElem?_eq_getElem (by simpa only [relationWords_length] using j.isLt)]
  simp [relationWords]

theorem tableWords_get_relation (table : Table q) (e : Fin table.darts)
    (j : Fin (q * q)) :
    (tableWords table)[rowOffset q e.val + 2 + j.val]? =
      some (bitWord table.rows[e].relation[j]) := by
  have h := congrArg (fun words : List Nat => words[j.val]?)
    (tableWords_drop_relation table e)
  rw [List.getElem?_drop,
    List.getElem?_append_left (by simpa only [relationWords_length] using j.isLt), relationWords_get] at h
  exact h

theorem tableWords_get_predicate (table : Table q) (e : Fin table.darts)
    (a b : Label q) :
    (tableWords table)[rowOffset q e.val + 2 + (b.val + q * a.val)]? =
      some (bitWord ((semantics table).accepts e a b)) := by
  simpa only [relationIndex_val, semantics_accepts, relationAt] using
    tableWords_get_relation table e ((relationIndex q) (a, b))

theorem rowOffset_lt_length (table : Table q) (e : Fin table.darts) :
    rowOffset q e.val < (tableWords table).length := by
  rw [tableWords_length]
  have h := Nat.mul_le_mul_left (rowWidth q) (Nat.succ_le_of_lt e.isLt)
  rw [Nat.mul_succ] at h
  unfold rowOffset rowWidth at *
  omega

theorem relationOffset_lt_length (table : Table q) (e : Fin table.darts)
    (j : Fin (q * q)) :
    rowOffset q e.val + 2 + j.val < (tableWords table).length := by
  rw [tableWords_length]
  have h := Nat.mul_le_mul_left (rowWidth q) (Nat.succ_le_of_lt e.isLt)
  rw [Nat.mul_succ] at h
  have hj := j.isLt
  unfold rowOffset rowWidth at *
  omega

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Input

end OAI
