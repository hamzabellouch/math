import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.FinalCNFPattern
import OAI.Combinatorics.IndependentSets.PCP.Ambient

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFTableAdapter

open PCP

def genericRow {n m : Nat} (row : GraphTables.DartRow n m) :
    GenericGraphTables.DartRow 64 n m :=
  ⟨row.tail, row.reverseIndex, row.relation⟩

@[simp] theorem genericRow_tail {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).tail = row.tail := rfl

@[simp] theorem genericRow_reverseIndex {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).reverseIndex = row.reverseIndex := rfl

@[simp] theorem genericRow_relation {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).relation = row.relation := rfl

def genericRows {n m : Nat} (rows : GraphTables.Rows n m) :
    GenericGraphTables.Rows 64 n m := rows.map genericRow

@[simp] theorem genericRows_get {n m : Nat} (rows : GraphTables.Rows n m) (e : Fin m) :
    (genericRows rows)[e] = genericRow rows[e] := by
  simp [genericRows]

@[simp] theorem genericRows_reverseAt {n m : Nat} (rows : GraphTables.Rows n m)
    (e : Fin m) :
    GenericGraphTables.reverseAt (genericRows rows) e = GraphTables.reverseAt rows e := by
  change (genericRows rows)[e].reverseIndex = rows[e].reverseIndex
  rw [genericRows_get]
  rfl

@[simp] theorem genericRows_acceptsAt {n m : Nat} (rows : GraphTables.Rows n m)
    (e : Fin m) (a b : Fin 64) :
    GenericGraphTables.acceptsAt (genericRows rows) e a b =
      GraphTables.acceptsAt rows e a b := by
  simp only [GenericGraphTables.acceptsAt, genericRows_get, genericRow_relation]
  rfl

theorem genericRows_valid {n m : Nat} (rows : GraphTables.Rows n m)
    (valid : GraphTables.Valid rows) : GenericGraphTables.Valid (genericRows rows) := by
  constructor
  · intro e
    simpa only [genericRows_reverseAt] using valid.1 e
  · intro e a b
    simpa only [genericRows_reverseAt, genericRows_acceptsAt] using valid.2 e a b

def genericTable (table : GraphTables.Table) : GenericGraphTables.Table 64 where
  vertices := table.vertices
  darts := table.darts
  rows := genericRows table.rows
  valid := genericRows_valid table.rows table.valid

@[simp] theorem genericTable_vertices (table : GraphTables.Table) :
    (genericTable table).vertices = table.vertices := rfl

@[simp] theorem genericTable_darts (table : GraphTables.Table) :
    (genericTable table).darts = table.darts := rfl

@[simp] theorem genericTable_row (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e] = genericRow table.rows[e] := genericRows_get _ _

@[simp] theorem genericTable_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].tail = table.rows[e].tail := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericTable_reverseIndex (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].reverseIndex = table.rows[e].reverseIndex := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericTable_relation (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].relation = table.rows[e].relation := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericRow_words {n m : Nat} (row : GraphTables.DartRow n m) :
    GenericGraphTables.rowWords (genericRow row) = GraphTables.rowWords row := rfl

theorem genericTable_rowList (table : GraphTables.Table) :
    GenericGraphTables.rowList (genericTable table) =
      (GraphTables.rowList table).map genericRow := by
  simp only [GenericGraphTables.rowList, GraphTables.rowList, genericTable,
    genericRows, Vector.toList_map]

@[simp] theorem genericTable_tableWords (table : GraphTables.Table) :
    GenericGraphTables.tableWords (genericTable table) = GraphTables.tableWords table := by
  simp only [GenericGraphTables.tableWords, GraphTables.tableWords,
    genericTable_vertices, genericTable_darts, genericTable_rowList, List.flatMap_map,
    genericRow_words]

@[simp] theorem genericTable_tableBits (table : GraphTables.Table) :
    GenericGraphTables.tableBits (genericTable table) = GraphTables.tableBits table := by
  simp only [GenericGraphTables.tableBits, GraphTables.tableBits, genericTable_tableWords]

@[simp] theorem genericTable_semantics_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).tail e =
      (GraphTables.semantics table).tail e := genericTable_tail table e

@[simp] theorem genericTable_semantics_reverse (table : GraphTables.Table)
    (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).reverse e =
      (GraphTables.semantics table).reverse e := genericTable_reverseIndex table e

@[simp] theorem genericTable_semantics_head (table : GraphTables.Table) (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).head e =
      (GraphTables.semantics table).head e := by
  exact (genericTable_semantics_tail table _).trans
    (congrArg (GraphTables.semantics table).tail (genericTable_semantics_reverse table e))

@[simp] theorem genericTable_semantics_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (a b : Fin 64) :
    (GenericGraphTables.semantics (genericTable table)).accepts e a b =
      (GraphTables.semantics table).accepts e a b := genericRows_acceptsAt _ _ _ _

@[simp] theorem genericTable_headIndex (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headIndex (genericTable table) e = table.rows[e].reverseIndex :=
  genericTable_reverseIndex table e

@[simp] theorem genericTable_headValue (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headValue (genericTable table) e =
      ((GraphTables.semantics table).head e).val := by
  exact (AlphabetTable.Lookup.headValue_eq_semantics (genericTable table) e).trans
    (congrArg Fin.val (genericTable_semantics_head table e))

theorem genericTable_headValue_tableGraph (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headValue (genericTable table) e =
      ((FinalCNFPattern.tableGraph table).head e).val := by
  rw [genericTable_headValue]
  rfl

theorem genericTable_pattern_relation (table : GraphTables.Table) (e : Fin table.darts)
    (p : VerifierToCNF.PatternIndex 12) :
    (genericTable table).rows[e].relation[FinalCNFPattern.patternRelationIndex p] =
      (FinalCNFPattern.tableVerifier table).accepts e (VerifierToCNF.patternAt 12 p) := by
  rw [genericTable_relation]
  exact FinalCNFPattern.pattern_lookup_eq_verifier_accepts table e p

end IndependentSetsGames.Foundations.Complexity.FinalCNFTableAdapter

end OAI
