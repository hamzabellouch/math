import OAI.Computability.BinPacking.Computation.FinalCNFRowTrace
import OAI.Computability.BinPacking.PCP.RoundTableGap

namespace OAI

namespace BinPackingGames.Foundations.Complexity.FinalCNFTemplate

open Target PCP

inductive Reference where
  | query : Fin 12 → Reference
  | auxiliary : Fin 9 → Reference
  deriving DecidableEq

structure LiteralTemplate where
  reference : Reference
  positive : Bool
  deriving DecidableEq

abbrev ClauseTemplate := Vector LiteralTemplate 3

def queryLiteral (bits : Fin 12 → Bool) (i : Fin 12) : LiteralTemplate :=
  ⟨.query i, !(bits i)⟩

def auxiliaryLiteral (j : Fin 9) (positive : Bool) : LiteralTemplate :=
  ⟨.auxiliary j, positive⟩

def tautologyTemplate : ClauseTemplate :=
  #v[⟨.query 0, true⟩, ⟨.query 0, false⟩, ⟨.query 0, true⟩]

def chainTemplates (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  #v[
    #v[queryLiteral bits 0, queryLiteral bits 1, auxiliaryLiteral 0 true],
    #v[auxiliaryLiteral 0 false, queryLiteral bits 2, auxiliaryLiteral 1 true],
    #v[auxiliaryLiteral 1 false, queryLiteral bits 3, auxiliaryLiteral 2 true],
    #v[auxiliaryLiteral 2 false, queryLiteral bits 4, auxiliaryLiteral 3 true],
    #v[auxiliaryLiteral 3 false, queryLiteral bits 5, auxiliaryLiteral 4 true],
    #v[auxiliaryLiteral 4 false, queryLiteral bits 6, auxiliaryLiteral 5 true],
    #v[auxiliaryLiteral 5 false, queryLiteral bits 7, auxiliaryLiteral 6 true],
    #v[auxiliaryLiteral 6 false, queryLiteral bits 8, auxiliaryLiteral 7 true],
    #v[auxiliaryLiteral 7 false, queryLiteral bits 9, auxiliaryLiteral 8 true],
    #v[auxiliaryLiteral 8 false, queryLiteral bits 10, queryLiteral bits 11]]

def blockTemplates (accepted : Bool) (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  if accepted then Vector.replicate 10 tautologyTemplate else chainTemplates bits

def templates (accepted : Bool) (bits : Fin 12 → Bool) : List ClauseTemplate :=
  (blockTemplates accepted bits).toList

def literalAt (accepted : Bool) (bits : Fin 12 → Bool)
    (clause : Fin 10) (slot : Fin 3) : LiteralTemplate :=
  (blockTemplates accepted bits)[clause][slot]

@[simp] theorem templates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (templates accepted bits).length = 10 := Vector.length_toList

theorem templates_true (bits : Fin 12 → Bool) :
    templates true bits = List.replicate 10 tautologyTemplate := by rfl

theorem templates_false (bits : Fin 12 → Bool) :
    templates false bits = (chainTemplates bits).toList := by rfl

def literalTemplates (accepted : Bool) (bits : Fin 12 → Bool) : List LiteralTemplate :=
  (templates accepted bits).flatMap fun clause => [clause[0], clause[1], clause[2]]

theorem literalTemplates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (literalTemplates accepted bits).length = 30 := by
  unfold literalTemplates
  rw [VerifierToCNF.length_flatMap_constant _ _ 3 (by intro c hc; rfl), templates_length]

def literalWords (index : Reference → Nat) (literal : LiteralTemplate) : List Nat :=
  [index literal.reference, if literal.positive then 1 else 0]

def clauseWords (index : Reference → Nat) (clause : ClauseTemplate) : List Nat :=
  literalWords index clause[0] ++ literalWords index clause[1] ++ literalWords index clause[2]

def words (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) : List Nat :=
  (templates accepted bits).flatMap (clauseWords index)

theorem words_length (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) :
    (words accepted bits index).length = 60 := by
  unfold words
  rw [VerifierToCNF.length_flatMap_constant _ _ 6
    (by intro c hc; simp [clauseWords, literalWords]), templates_length]

variable (V : VerifierToCNF.FiniteVerifier 12) (e : Fin V.events)
  (p : VerifierToCNF.PatternIndex 12)

def resolve : Reference → Fin (VerifierToCNF.outputVariables V)
  | .query i => VerifierToCNF.oldIndex V (V.query e i)
  | .auxiliary j => VerifierToCNF.freshIndex V e p j

theorem resolve_query_value (i : Fin 12) :
    (resolve V e p (.query i)).val = (V.query e i).val := by
  simp only [resolve, VerifierToCNF.oldIndex, Fin.val_castAdd]

theorem resolve_auxiliary_value (j : Fin 9) :
    (resolve V e p (.auxiliary j)).val =
      V.variables + ((e.val * 4096 + p.val) * 9 + j.val) := by
  change (VerifierToCNF.freshIndex V e p j).val = _
  exact (VerifierToCNF.freshIndex_value V e p j).trans
    (congrArg (fun k : Nat => V.variables + ((e.val * k + p.val) * 9 + j.val))
      (show (VerifierToCNF.patterns 12).length = 4096 from VerifierToCNF.patterns_length 12))

def instantiateLiteral (literal : LiteralTemplate) : Literal (VerifierToCNF.outputVariables V) :=
  ⟨resolve V e p literal.reference, literal.positive⟩

def instantiateClause (clause : ClauseTemplate) : Clause (VerifierToCNF.outputVariables V) :=
  #v[instantiateLiteral V e p clause[0], instantiateLiteral V e p clause[1],
    instantiateLiteral V e p clause[2]]

theorem splitLong_twelve {n : Nat} (ls : Fin 12 → Literal n) (ys : Fin 9 → Fin n) :
    VerifierToCNF.splitLong (List.ofFn ls) (List.ofFn ys) =
      [#v[ls 0, ls 1, ⟨ys 0, true⟩],
       #v[⟨ys 0, false⟩, ls 2, ⟨ys 1, true⟩],
       #v[⟨ys 1, false⟩, ls 3, ⟨ys 2, true⟩],
       #v[⟨ys 2, false⟩, ls 4, ⟨ys 3, true⟩],
       #v[⟨ys 3, false⟩, ls 5, ⟨ys 4, true⟩],
       #v[⟨ys 4, false⟩, ls 6, ⟨ys 5, true⟩],
       #v[⟨ys 5, false⟩, ls 7, ⟨ys 6, true⟩],
       #v[⟨ys 6, false⟩, ls 8, ⟨ys 7, true⟩],
       #v[⟨ys 7, false⟩, ls 9, ⟨ys 8, true⟩],
       #v[⟨ys 8, false⟩, ls 10, ls 11]] := by
  simp only [List.ofFn_succ, List.ofFn_zero, VerifierToCNF.splitLong]
  rfl

theorem instantiate_templates :
    (templates (V.accepts e (VerifierToCNF.patternAt 12 p))
      (VerifierToCNF.patternAt 12 p)).map (instantiateClause V e p) =
        VerifierToCNF.block V (by decide) e p := by
  cases h : V.accepts e (VerifierToCNF.patternAt 12 p) with
  | false =>
      simp only [h, templates_false, VerifierToCNF.block, Bool.false_eq_true, ↓reduceIte,
        VerifierToCNF.forbiddenClause, VerifierToCNF.auxiliaryNames]
      rw [splitLong_twelve]
      rfl
  | true =>
      simp only [h, templates_true, VerifierToCNF.block, ↓reduceIte, List.map_replicate]
      rfl

theorem instantiate_templates_of_acceptance (accepted : Bool)
    (h : V.accepts e (VerifierToCNF.patternAt 12 p) = accepted) :
    (templates accepted (VerifierToCNF.patternAt 12 p)).map (instantiateClause V e p) =
      VerifierToCNF.block V (by decide) e p := by
  rw [← h]
  exact instantiate_templates V e p

theorem instantiateClause_words (clause : ClauseTemplate) :
    Complexity.clauseWords (instantiateClause V e p clause) =
      clauseWords (fun r => (resolve V e p r).val) clause := rfl

theorem words_eq_block :
    words (V.accepts e (VerifierToCNF.patternAt 12 p)) (VerifierToCNF.patternAt 12 p)
      (fun r => (resolve V e p r).val) =
        (VerifierToCNF.block V (by decide) e p).flatMap Complexity.clauseWords := by
  rw [← instantiate_templates V e p]
  simp only [List.flatMap_map, instantiateClause_words]
  rfl

theorem block_words_length :
    ((VerifierToCNF.block V (by decide) e p).flatMap Complexity.clauseWords).length = 60 := by
  rw [← words_eq_block V e p]
  exact words_length _ _ _

end BinPackingGames.Foundations.Complexity.FinalCNFTemplate

namespace BinPackingGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev Label := FinalBooleanVerifier.Label

abbrev labelEquiv : Label ≃ Fin 64 := AlphabetTable.Enumeration.labelEquiv

theorem labelEquiv_val (label : Label) :
    (labelEquiv label).val =
      ∑ i : Fin 6, AlphabetTable.Enumeration.bitValue (label i) * 2 ^ i.val :=
  AlphabetTable.Enumeration.labelEquiv_val label

def labelIndex (label : Label) : Fin 64 := labelEquiv label

def labelBits (index : Fin 64) : Label := labelEquiv.symm index

@[simp] theorem labelBits_labelIndex (label : Label) :
    labelBits (labelIndex label) = label := labelEquiv.symm_apply_apply label

@[simp] theorem labelIndex_labelBits (index : Fin 64) :
    labelIndex (labelBits index) = index := labelEquiv.apply_symm_apply index

def leftHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.castAdd 6 j)

def rightHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.natAdd 6 j)

def relationAddress (bits : VerifierToCNF.Pattern 12) : Fin 4096 :=
  GraphTables.relationIndex (labelIndex (leftHalf bits), labelIndex (rightHalf bits))

theorem relationAddress_val (bits : VerifierToCNF.Pattern 12) :
    (relationAddress bits).val =
      64 * (labelIndex (leftHalf bits)).val + (labelIndex (rightHalf bits)).val := by
  rw [relationAddress, GraphTables.relationIndex_val, Nat.add_comm]

def patternRelationIndex (p : VerifierToCNF.PatternIndex 12) : Fin 4096 :=
  relationAddress (VerifierToCNF.patternAt 12 p)

@[simp] theorem patternRelationIndex_eq (p : VerifierToCNF.PatternIndex 12) :
    patternRelationIndex p = relationAddress (VerifierToCNF.patternAt 12 p) := rfl

def tableGraph (table : GraphTables.Table) :
    ConstraintGraph (Fin table.vertices) (Fin table.darts) Label :=
  (GraphTables.semantics table).reindex (Equiv.refl _) (Equiv.refl _) labelEquiv.symm

@[simp] theorem tableGraph_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).tail e = table.rows[e].tail := rfl

@[simp] theorem tableGraph_reverse (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem tableGraph_accepts (table : GraphTables.Table) (e : Fin table.darts)
    (a b : Label) :
    (tableGraph table).accepts e a b =
      GraphTables.relationAt table.rows[e].relation (labelIndex a) (labelIndex b) := rfl

abbrev tableVerifier (table : GraphTables.Table) : VerifierToCNF.FiniteVerifier 12 :=
  FinalBooleanVerifier.verifier (tableGraph table) (Equiv.refl _) (Equiv.refl _)

theorem relation_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (bits : VerifierToCNF.Pattern 12) :
    table.rows[e].relation[relationAddress bits] =
      (tableVerifier table).accepts e bits := rfl

theorem pattern_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (p : VerifierToCNF.PatternIndex 12) :
    table.rows[e].relation[patternRelationIndex p] =
      (tableVerifier table).accepts e (VerifierToCNF.patternAt 12 p) := rfl

theorem verifier_accepts_eq_lookup (table : GraphTables.Table)
    (e : Fin table.darts) (bits : VerifierToCNF.Pattern 12) :
    (tableVerifier table).accepts e bits =
      table.rows[e].relation[relationAddress bits] := rfl

theorem buffer_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (buffer : Fin 4096 → Bool)
    (read_correct : ∀ i, buffer i = table.rows[e].relation[i])
    (bits : VerifierToCNF.Pattern 12) :
    buffer (relationAddress bits) = (tableVerifier table).accepts e bits :=
  (read_correct _).trans (relation_lookup_eq_verifier_accepts table e bits)

theorem pattern_buffer_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (buffer : Fin 4096 → Bool)
    (read_correct : ∀ i, buffer i = table.rows[e].relation[i])
    (p : VerifierToCNF.PatternIndex 12) :
    buffer (patternRelationIndex p) =
      (tableVerifier table).accepts e (VerifierToCNF.patternAt 12 p) :=
  buffer_lookup_eq_verifier_accepts table e buffer read_correct _

end BinPackingGames.Foundations.Complexity.FinalCNFPattern

namespace BinPackingGames.Foundations.Complexity.FinalCNFTableAdapter

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
  simp only [ConstraintGraph.head, genericTable_semantics_reverse, genericTable_semantics_tail]
  rfl

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

end BinPackingGames.Foundations.Complexity.FinalCNFTableAdapter

namespace BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTemplate

def referenceValue (vertices tail head row pattern : Nat) : Reference → Nat
  | .query i => if i.val < 6 then 6 * tail + i.val else 6 * head + (i.val - 6)
  | .auxiliary j => 6 * vertices + 36864 * row + (9 * pattern + j.val)

def auxiliaryFlag : Reference → Bool
  | .query _ => false
  | .auxiliary _ => true

def tailFlag : Reference → Bool
  | .query i => decide (i.val < 6)
  | .auxiliary _ => false

def headFlag : Reference → Bool
  | .query i => decide (6 ≤ i.val)
  | .auxiliary _ => false

theorem pattern_lt (p : VerifierToCNF.PatternIndex 12) : p.val < 4096 := by
  have hlen : (VerifierToCNF.patterns 12).length = 4096 := VerifierToCNF.patterns_length 12
  exact lt_of_lt_of_eq p.isLt hlen

def referenceOffset (p : VerifierToCNF.PatternIndex 12) : Reference → Fin 36864
  | .query i => ⟨if i.val < 6 then i.val else i.val - 6, by split <;> omega⟩
  | .auxiliary j => ⟨9 * p.val + j.val, by have hp := pattern_lt p; omega⟩

def literalPlan (p : VerifierToCNF.PatternIndex 12) (literal : Ambient → LiteralTemplate) : Plan :=
  [.scaledIf 0 6 (fun state => auxiliaryFlag (literal state).reference),
   .scaledIf 2 6 (fun state => tailFlag (literal state).reference),
   .scaledIf 3 6 (fun state => headFlag (literal state).reference),
   .scaledIf 4 36864 (fun state => auxiliaryFlag (literal state).reference),
   .bounded (fun state => referenceOffset p (literal state).reference),
   .literal [false],
   .bit (fun state => (literal state).positive)]

theorem literalPlan_length (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) : (literalPlan p literal).length = 7 := rfl

theorem literalPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) (vertices darts tail head row : Nat)
    (ambient : Ambient) :
    (literalPlan p literal).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.literalWords
        (referenceValue vertices tail head row p.val) (literal ambient)) := by
  rcases h : literal ambient with ⟨reference, positive⟩
  cases reference with
  | query i =>
      by_cases hi : i.val < 6
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show ¬ 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
  | auxiliary j =>
      simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
        referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
        encodeWords, encodeWord, List.replicate_add, List.append_assoc,
        -List.replicate_append_replicate]
      rfl

def patternLiteral (p : VerifierToCNF.PatternIndex 12) (clause : Fin 10) (slot : Fin 3)
    (ambient : Ambient) : LiteralTemplate :=
  literalAt (ambient.2 (FinalCNFPattern.patternRelationIndex p))
    (VerifierToCNF.patternAt 12 p) clause slot

def patternPlan (p : VerifierToCNF.PatternIndex 12) : Plan :=
  (List.finRange 10).flatMap fun clause =>
    (List.finRange 3).flatMap fun slot => literalPlan p (patternLiteral p clause slot)

def rowPlan : Plan :=
  (List.finRange (VerifierToCNF.patterns 12).length).flatMap patternPlan

theorem patternPlan_length (p : VerifierToCNF.PatternIndex 12) :
    (patternPlan p).length = 210 := by
  unfold patternPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 21]
  · simp
  · intro clause hclause
    rw [VerifierToCNF.length_flatMap_constant _ _ 7]
    · simp
    · intro slot hslot
      exact literalPlan_length _ _

theorem rowPlan_length : rowPlan.length = 860160 := by
  unfold rowPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 210]
  · rw [List.length_finRange, VerifierToCNF.patterns_length]
    norm_num
  · intro p hp
    exact patternPlan_length p

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem patternPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (vertices darts tail head row : Nat) (ambient : Ambient) :
    (patternPlan p).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.words
        (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) (referenceValue vertices tail head row p.val)) := by
  unfold patternPlan
  simp only [List.flatMap_assoc]
  simp_rw [literalPlan_bits]
  have hclauses :
      (List.finRange 10).map
        (fun c => (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
          (VerifierToCNF.patternAt 12 p))[c]) =
      templates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) := by
    rw [← List.ofFn_eq_map]
    change List.ofFn (fun c : Fin 10 =>
      (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p))[c.val]) = _
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
    rfl
  unfold FinalCNFTemplate.words
  rw [← hclauses, List.flatMap_map, encodeWords_flatMap]
  apply List.flatMap_congr
  intro clause hclause
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.flatMap_cons,
    List.flatMap_nil, patternLiteral, literalAt, FinalCNFTemplate.clauseWords,
    encodeWords_append, List.append_nil, List.append_assoc]
  rfl

theorem referenceValue_eq_resolve (table : GraphTables.Table) (e : Fin table.darts)
    (p : VerifierToCNF.PatternIndex 12) (reference : Reference) :
    referenceValue table.vertices table.rows[e].tail.val
      table.rows[table.rows[e].reverseIndex].tail.val e.val p.val reference =
      (resolve (FinalCNFPattern.tableVerifier table) e p reference).val := by
  cases reference with
  | query i =>
      rw [resolve_query_value]
      refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
      · rw [FinalBooleanVerifier.query_tail]
        simp only [referenceValue, Fin.val_castAdd, j.isLt, ite_true]
        change 6 * table.rows[e].tail.val + j.val = j.val + 6 * table.rows[e].tail.val
        omega
      · rw [FinalBooleanVerifier.query_head]
        simp only [referenceValue, Fin.val_natAdd]
        split
        · omega
        · change 6 * table.rows[table.rows[e].reverseIndex].tail.val +
              (6 + j.val - 6) = j.val + 6 * table.rows[table.rows[e].reverseIndex].tail.val
          omega
  | auxiliary j =>
      rw [resolve_auxiliary_value]
      change 6 * table.vertices + 36864 * e.val + (9 * p.val + j.val) =
        table.vertices * 6 + ((e.val * 4096 + p.val) * 9 + j.val)
      omega

theorem rowPlan_bits (table : GraphTables.Table) (e : Fin table.darts) :
    rowPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts table.rows[e].tail.val
        table.rows[table.rows[e].reverseIndex].tail.val e.val)
      ((), fun i => table.rows[e].relation[i])) =
      encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
        (by decide) e).flatMap Complexity.clauseWords) := by
  unfold rowPlan VerifierToCNF.eventBlock
  simp only [List.flatMap_assoc]
  rw [encodeWords_flatMap]
  apply List.flatMap_congr
  intro p hp
  rw [patternPlan_bits]
  dsimp only
  rw [FinalCNFPattern.pattern_lookup_eq_verifier_accepts]
  have href := funext (referenceValue_eq_resolve table e p)
  rw [href]
  exact congrArg encodeWords (words_eq_block (FinalCNFPattern.tableVerifier table) e p)

end BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
