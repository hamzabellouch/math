import Mathlib
import OAI.Computability.MaxCut.Machines.AlphabetGraph

namespace OAI


namespace MaxCutGames.Foundations.PCP.AlphabetTable.Relations

open Hastad
open Queries

variable {q : Nat}

/-- Exact local address comparison. A loop identifies the two endpoint tables;
the joint edge table is always disjoint from every endpoint table. -/
def sameAddress (selfLoop : Bool) : RawQuery q → RawQuery q → Bool
  | .inl (side, f), .inl (side', g) => ((side == side') || selfLoop) && decide (f = g)
  | .inr f, .inr g => decide (f = g)
  | _, _ => false

@[simp] theorem sameAddress_refl (selfLoop : Bool) (x : RawQuery q) :
    sameAddress selfLoop x x = true := by
  rcases x with ⟨side, f⟩ | f <;> simp [sameAddress]

theorem globalize_eq_iff {V E : Type*} [DecidableEq V]
    (tail head : V) (edge : E) (selfLoop : Bool)
    (hloop : selfLoop = decide (tail = head)) (x y : RawQuery q) :
    globalize tail head edge x = globalize tail head edge y ↔
      sameAddress selfLoop x y = true := by
  rcases x with ⟨side, f⟩ | f <;> rcases y with ⟨side', g⟩ | g
  · cases side <;> cases side'
    · simp [globalize, sameAddress]
    · simp [globalize, sameAddress, hloop]
    · simp [globalize, sameAddress, hloop,
        show head = tail ↔ tail = head from eq_comm]
    · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]

def eqProfile (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i j : Fin 6) : Bool := sameAddress selfLoop (queries i) (queries j)

@[simp] theorem eqProfile_refl (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i : Fin 6) : eqProfile selfLoop queries i i = true := sameAddress_refl _ _

/-- Search the fixed six positions for the least occurrence of an address. -/
def canonicalSlot (selfLoop : Bool) (queries : Fin 6 → RawQuery q) (i : Fin 6) : Fin 6 :=
  Fin.find (fun j => eqProfile selfLoop queries j i = true) ⟨i, eqProfile_refl _ _ _⟩

theorem canonicalSlot_profile (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i : Fin 6) : eqProfile selfLoop queries (canonicalSlot selfLoop queries i) i = true := by
  unfold canonicalSlot
  exact Fin.find_spec (p := fun j => eqProfile selfLoop queries j i = true)
    ⟨i, eqProfile_refl _ _ _⟩

theorem canonicalSlot_le (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i j : Fin 6) (h : eqProfile selfLoop queries j i = true) :
    canonicalSlot selfLoop queries i ≤ j :=
  Fin.find_le_of_pos ⟨i, eqProfile_refl _ _ _⟩ h

def RepeatedConsistent (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Prop :=
  ∀ i j, eqProfile selfLoop queries i j = true → label i = label j

instance repeatedConsistentDecidable (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Decidable (RepeatedConsistent selfLoop queries label) := by
  unfold RepeatedConsistent
  infer_instance

def incidenceAccept (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) : Bool :=
  decide (accept left = true ∧ RepeatedConsistent selfLoop queries left) &&
    decide (left (canonicalSlot selfLoop queries slot) = right 0)

def predicate (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6) (orientation : Bool)
    (a b : QueryIncidence.Label 6) : Bool :=
  if orientation then incidenceAccept selfLoop queries accept slot b a
  else incidenceAccept selfLoop queries accept slot a b

/-- A complete 64-by-64 Boolean relation in the shared row-major table format. -/
def relation (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool) :
    GraphTables.RelationTable :=
  GraphTables.relationOf fun a b =>
    predicate selfLoop (query P event) (AssignmentTester.eventAccepts event.1)
      slot orientation (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b)

@[simp] theorem relationAt_relation (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt (relation P selfLoop event slot orientation) a b =
      predicate selfLoop (query P event) (AssignmentTester.eventAccepts event.1)
        slot orientation (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b) := by
  exact GraphTables.relationAt_relationOf _ _ _

theorem relation_reverse (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt (relation P selfLoop event slot (!orientation)) b a =
      GraphTables.relationAt (relation P selfLoop event slot orientation) a b := by
  simp only [relationAt_relation]
  cases orientation <;> rfl

/-- The old predicate is read in the same row-major order as a graph row. -/
def oldPredicate (old : Vector Bool (q * q)) (a b : Fin q) : Bool :=
  old[(finProdFinEquiv (a, b) : Fin (q * q))]

def relationFromTable (old : Vector Bool (q * q)) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool) :
    GraphTables.RelationTable := relation (oldPredicate old) selfLoop event slot orientation

@[simp] theorem oldPredicate_relationAt (old : GraphTables.RelationTable)
    (a b : GraphTables.Label) : oldPredicate old a b = GraphTables.relationAt old a b := rfl

theorem relationFromTable_eq (old : GraphTables.RelationTable) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin 64)) (slot : Fin 6) (orientation : Bool) :
    relationFromTable old selfLoop event slot orientation =
      relation (GraphTables.relationAt old) selfLoop event slot orientation := rfl


variable {V E : Type*} [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem eqProfile_query_iff (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (i j : Fin 6) :
    eqProfile (decide (G.tail e = G.head e)) (query (G.accepts e) event) i j = true ↔
      (AlphabetGraph.verifier G).query (e, event) i =
        (AlphabetGraph.verifier G).query (e, event) j := by
  rw [← globalize_query G e event i, ← globalize_query G e event j]
  exact (globalize_eq_iff (G.tail e) (G.head e) e _ rfl _ _).symm

theorem canonicalSlot_eq (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    canonicalSlot (decide (G.tail e = G.head e)) (query (G.accepts e) event) slot =
      QueryIncidence.canonicalSlot (AlphabetGraph.verifier G) (e, event) slot := by
  unfold canonicalSlot QueryIncidence.canonicalSlot
  apply Fin.find_congr'
  exact eqProfile_query_iff G e event _ slot

omit [DecidableEq E] in
theorem repeatedConsistent_iff (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (label : QueryIncidence.Label 6) :
    RepeatedConsistent (decide (G.tail e = G.head e)) (query (G.accepts e) event) label ↔
      QueryIncidence.RepeatedConsistent (AlphabetGraph.verifier G) (e, event) label := by
  constructor
  · intro h i j hij
    exact h i j ((eqProfile_query_iff G e event i j).mpr hij)
  · intro h i j hij
    exact h i j ((eqProfile_query_iff G e event i j).mp hij)

omit [DecidableEq V] [DecidableEq E] in
theorem verifier_accepts (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (label : QueryIncidence.Label 6) :
    (AlphabetGraph.verifier G).accepts (e, event) label =
      AssignmentTester.eventAccepts event.1 label := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  rfl

theorem incidenceAccept_eq (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) :
    incidenceAccept (decide (G.tail e = G.head e)) (query (G.accepts e) event)
      (AssignmentTester.eventAccepts event.1) slot left right =
      QueryIncidence.incidenceAccept (AlphabetGraph.verifier G) (by decide) (e, event) slot
        left right := by
  simp only [incidenceAccept, QueryIncidence.incidenceAccept, QueryIncidence.LeftValid,
    verifier_accepts, repeatedConsistent_iff, canonicalSlot_eq,
    QueryIncidence.decodeRight, QueryIncidence.zeroSlot]
  rfl

/-- Every stored bit is the actual six-query incidence predicate under the
canonical explicit six-bit label enumeration, including loops and repeats. -/
theorem relationAt_relation_graph (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt
        (relation (G.accepts e) (decide (G.tail e = G.head e)) event slot orientation) a b =
      (AlphabetGraph.graph G).accepts (((e, event), slot), orientation)
        (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b) := by
  rw [relationAt_relation]
  cases orientation <;>
    exact incidenceAccept_eq G e event slot _ _


end MaxCutGames.Foundations.PCP.AlphabetTable.Relations


namespace MaxCutGames.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

/-- One directed occurrence, without merging repeated queries or equal rows. -/
def rowFromDart (input : GenericGraphTables.Table q)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    GraphTables.DartRow (Enumeration.vertexCount input.vertices input.darts q)
      (Enumeration.dartCount input.darts q) :=
  let edge := dart.1.1.1
  let event := dart.1.1.2
  let slot := dart.1.2
  let old := input.rows[edge]
  let head := input.rows[old.reverseIndex].tail
  { tail := Enumeration.vertexEquiv input.vertices input.darts q
      (if dart.2 then
        .inr (Queries.globalize old.tail head edge
          (Queries.query (GenericGraphTables.relationAt old.relation) event slot))
      else .inl (edge, event))
    reverseIndex := Enumeration.dartEquiv input.darts q (dart.1, !dart.2)
    relation := Relations.relationFromTable old.relation (decide (old.tail = head))
      event slot dart.2 }

/-- The row number decodes to precisely one event/slot/orientation occurrence. -/
def rows (input : GenericGraphTables.Table q) :
    GraphTables.Rows (Enumeration.vertexCount input.vertices input.darts q)
      (Enumeration.dartCount input.darts q) :=
  Vector.ofFn (fun index =>
    rowFromDart input ((Enumeration.dartEquiv input.darts q).symm index))

@[simp] theorem rows_at (input : GenericGraphTables.Table q)
    (index : Fin (Enumeration.dartCount input.darts q)) :
    (rows input)[index] =
      rowFromDart input ((Enumeration.dartEquiv input.darts q).symm index) := by
  simp [rows]

/-- Reversal changes only the occurrence's orientation, preserving event and slot. -/
theorem rows_reverseIndex (input : GenericGraphTables.Table q)
    (index : Fin (Enumeration.dartCount input.darts q)) :
    (rows input)[index].reverseIndex =
      Enumeration.dartEquiv input.darts q
        (((Enumeration.dartEquiv input.darts q).symm index).1,
          !((Enumeration.dartEquiv input.darts q).symm index).2) := by
  simp [rows, rowFromDart]

private theorem dartRow_ext_inline_Table {n m : Nat} {left right : GraphTables.DartRow n m}
    (ht : left.tail = right.tail) (hr : left.reverseIndex = right.reverseIndex)
    (hp : left.relation = right.relation) : left = right := by
  cases left
  cases right
  cases ht
  cases hr
  cases hp
  rfl

private theorem relation_ext_inline_Table {left right : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt left a b = GraphTables.relationAt right a b) :
    left = right := by
  apply Vector.ext
  intro i hi
  let labels := GraphTables.relationIndex.symm (⟨i, hi⟩ : Fin 4096)
  have index : GraphTables.relationIndex labels = (⟨i, hi⟩ : Fin 4096) :=
    GraphTables.relationIndex.apply_symm_apply _
  have point := h labels.1 labels.2
  simpa only [GraphTables.relationAt, index, Fin.getElem_fin] using point

section Semantics

/-- The three stored fields agree with the actual alphabet graph at this dart. -/
theorem rowFromDart_eq_graphRow (input : GenericGraphTables.Table q)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    rowFromDart input dart =
      { tail := Enumeration.vertexEquiv input.vertices input.darts q
          ((AlphabetGraph.graph (GenericGraphTables.semantics input)).tail dart)
        reverseIndex := Enumeration.dartEquiv input.darts q
          ((AlphabetGraph.graph (GenericGraphTables.semantics input)).reverse dart)
        relation := GraphTables.relationOf (fun a b =>
          (AlphabetGraph.graph (GenericGraphTables.semantics input)).accepts dart
            (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b)) } := by
  rcases dart with ⟨⟨⟨edge, event⟩, slot⟩, orientation⟩
  apply dartRow_ext_inline_Table
  · cases orientation with
    | false => rfl
    | true =>
      have query := Queries.globalize_query (GenericGraphTables.semantics input)
        edge event slot
      have predicate : (GenericGraphTables.semantics input).accepts edge =
          GenericGraphTables.relationAt input.rows[edge].relation := rfl
      rw [predicate] at query
      simpa only [rowFromDart, AlphabetGraph.graph, QueryIncidence.graph,
        QueryIncidence.tail, GenericGraphTables.semantics_tail,
        ConstraintGraph.head, GenericGraphTables.semantics_reverse,
        ite_true] using
        congrArg (fun address => Enumeration.vertexEquiv input.vertices input.darts q
          (.inr address)) query
  · rfl
  · apply relation_ext_inline_Table
    intro a b
    rw [GraphTables.relationAt_relationOf]
    have relation := Relations.relationAt_relation_graph (GenericGraphTables.semantics input)
      edge event slot orientation a b
    have predicate : (GenericGraphTables.semantics input).accepts edge =
        Relations.oldPredicate input.rows[edge].relation := rfl
    rw [predicate] at relation

    simpa only [rowFromDart, Relations.relationFromTable,
      GenericGraphTables.semantics_tail, ConstraintGraph.head,
      GenericGraphTables.semantics_reverse] using! relation

/-- Equality of the full row vector, including all multiplicities and reversal indices. -/
theorem rows_eq_graphRows (input : GenericGraphTables.Table q) :
    rows input = GraphTables.graphRows
      (GraphTables.enumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv) := by
  apply Vector.ext
  intro i hi
  simp only [rows, GraphTables.graphRows, Vector.getElem_ofFn]
  exact rowFromDart_eq_graphRow input
    ((Enumeration.dartEquiv input.darts q).symm ⟨i, hi⟩)

theorem rows_valid (input : GenericGraphTables.Table q) : GraphTables.Valid (rows input) := by
  rw [rows_eq_graphRows]
  exact GraphTables.graphRows_valid _

/-- Actual executable output table. Its validity proof is erased at execution. -/
def build (input : GenericGraphTables.Table q) : GraphTables.Table where
  vertices := Enumeration.vertexCount input.vertices input.darts q
  darts := Enumeration.dartCount input.darts q
  rows := rows input
  valid := rows_valid input

@[simp] theorem build_vertices (input : GenericGraphTables.Table q) :
    (build input).vertices = Enumeration.vertexCount input.vertices input.darts q := rfl

@[simp] theorem build_darts (input : GenericGraphTables.Table q) :
    (build input).darts = Enumeration.dartCount input.darts q := rfl

private theorem table_rows_congr_inline_Table {n m : Nat} {left right : GraphTables.Rows n m}
    (h : left = right) (hl : GraphTables.Valid left) (hr : GraphTables.Valid right) :
    (⟨n, m, left, hl⟩ : GraphTables.Table) = ⟨n, m, right, hr⟩ := by
  subst right
  rfl

private theorem semantics_rows_congr_inline_Table {n m : Nat} {left right : GraphTables.Rows n m}
    (h : left = right) (hl : GraphTables.Valid left) (hr : GraphTables.Valid right) :
    GraphTables.semantics (⟨n, m, left, hl⟩ : GraphTables.Table) =
      GraphTables.semantics (⟨n, m, right, hr⟩ : GraphTables.Table) := by
  subst right
  rfl

/-- Exact table equality in the explicit enumerations, without a representation choice. -/
theorem build_eq_ofEnumeratedGraph (input : GenericGraphTables.Table q) :
    build input =
      GraphTables.ofEnumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv := by
  exact table_rows_congr_inline_Table (rows_eq_graphRows input) (rows_valid input)
    (GraphTables.graphRows_valid _)

/-- Full decoded graph equality, including reversal, endpoints, and every predicate bit. -/
theorem semantics_build (input : GenericGraphTables.Table q) :
    GraphTables.semantics (build input) =
      GraphTables.enumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv := by
  exact (semantics_rows_congr_inline_Table (rows_eq_graphRows input) (rows_valid input)
    (GraphTables.graphRows_valid _)).trans (GraphTables.semantics_ofGraph _)

/-- Encoding and decoding the executable output recovers the full intended table. -/
theorem decode_build (input : GenericGraphTables.Table q) :
    GraphTables.decodeTableBits (GraphTables.tableBits (build input)) =
      some (GraphTables.ofEnumeratedGraph
        (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv) := by
  rw [GraphTables.decodeTableBits_encoded, build_eq_ofEnumeratedGraph]

theorem edgeSatisfied_build (input : GenericGraphTables.Table q)
    (labeling : QueryIncidence.Vertex (AlphabetGraph.Event (Fin input.darts) (Fin q))
      (AlphabetGraph.Address (Fin input.vertices) (Fin input.darts) (Fin q)) →
        QueryIncidence.Label 6)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    (GraphTables.semantics (build input)).edgeSatisfied
      (fun v => Enumeration.labelEquiv
        (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v)))
      (Enumeration.dartEquiv input.darts q dart) =
        (AlphabetGraph.graph (GenericGraphTables.semantics input)).edgeSatisfied labeling dart := by
  rw [semantics_build]
  exact GraphTables.enumeratedGraph_edgeSatisfied _ _ _ _ labeling dart

theorem rejectionCount_build (input : GenericGraphTables.Table q)
    (labeling : QueryIncidence.Vertex (AlphabetGraph.Event (Fin input.darts) (Fin q))
      (AlphabetGraph.Address (Fin input.vertices) (Fin input.darts) (Fin q)) →
        QueryIncidence.Label 6) :
    (GraphTables.semantics (build input)).rejectionCount
      (fun v => Enumeration.labelEquiv
        (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) =
        (AlphabetGraph.graph (GenericGraphTables.semantics input)).rejectionCount labeling := by
  rw [semantics_build]
  exact GraphTables.enumeratedGraph_rejectionCount _ _ _ _ labeling

theorem perfect_completeness [Nonempty (Fin q)] (input : GenericGraphTables.Table q)
    (satisfied : (GenericGraphTables.semantics input).Satisfiable) :
    (GraphTables.semantics (build input)).Satisfiable := by
  obtain ⟨labeling, accepted⟩ :=
    AlphabetGraph.perfect_completeness (GenericGraphTables.semantics input) satisfied
  refine ⟨fun v => Enumeration.labelEquiv
    (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v)), ?_⟩
  intro index
  have h := edgeSatisfied_build input labeling
    ((Enumeration.dartEquiv input.darts q).symm index)
  have index_eq := (Enumeration.dartEquiv input.darts q).apply_symm_apply index
  rw [index_eq] at h
  exact h.trans (accepted _)

/-- The gap statement transfers to every labeling of the actual numbered table. -/
theorem gap_transfer [Nonempty (Fin q)] (input : GenericGraphTables.Table q) (a b : Nat)
    (source : ∀ labeling : Fin input.vertices → Fin q,
      a * input.darts ≤ b * (GenericGraphTables.semantics input).rejectionCount labeling)
    (labeling : Fin (build input).vertices → GraphTables.Label) :
    a * (build input).darts ≤
      (b * 12288) * (GraphTables.semantics (build input)).rejectionCount labeling := by
  classical
  let lifted := fun vertex => Enumeration.labelEquiv.symm
    (labeling (Enumeration.vertexEquiv input.vertices input.darts q vertex))
  have h := AlphabetGraph.gap_transfer (GenericGraphTables.semantics input) a b
    (by simpa only [Fintype.card_fin] using source) lifted
  rw [Enumeration.card_dart] at h
  have counts := rejectionCount_build input lifted
  have restored : (fun v : Fin (build input).vertices => Enumeration.labelEquiv
      (lifted ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) = labeling := by
    funext v
    dsimp only [lifted]
    rw [Enumeration.labelEquiv.apply_symm_apply]
    exact congrArg labeling
      ((Enumeration.vertexEquiv input.vertices input.darts q).apply_symm_apply v)
  rw [restored] at counts
  rw [← counts] at h
  exact h

/-- The serialized row list follows the same explicit occurrence order as the vector. -/
theorem rowList_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.rowList (build input) =
      (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).map
        (rowFromDart input) := by
  change (Vector.ofFn (fun index => rowFromDart input
      ((Enumeration.dartEquiv input.darts q).symm index))).toList =
    (List.ofFn (Enumeration.dartEquiv input.darts q).symm).map (rowFromDart input)
  simp only [Vector.toList_ofFn, List.map_ofFn, Function.comp_def]

/-- Complete output words: two headers followed by every ordered row block. -/
theorem tableWords_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.tableWords (build input) =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] ++
        (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).flatMap
          (fun dart => GraphTables.rowWords (rowFromDart input dart)) := by
  simp only [GraphTables.tableWords, rowList_eq_ordered, build_vertices, build_darts,
    List.flatMap_map]

@[simp] theorem rowList_length (input : GenericGraphTables.Table q) :
    (GraphTables.rowList (build input)).length = Enumeration.dartCount input.darts q := by
  exact GraphTables.rowList_length (build input)

theorem tableWords_length (input : GenericGraphTables.Table q) :
    (GraphTables.tableWords (build input)).length =
      2 + 4098 * Enumeration.dartCount input.darts q := by
  exact GraphTables.tableWords_length (build input)

theorem tableBits_length_le (input : GenericGraphTables.Table q) :
    (GraphTables.tableBits (build input)).length ≤
      Enumeration.vertexCount input.vertices input.darts q +
        Enumeration.dartCount input.darts q + 2 + Enumeration.dartCount input.darts q *
          (Enumeration.vertexCount input.vertices input.darts q +
            Enumeration.dartCount input.darts q + 8192) := by
  exact GraphTables.tableBits_length_le (build input)

end Semantics

end MaxCutGames.Foundations.PCP.AlphabetTable.Table


/-!
# Real gap and exact size of the alphabet graph

The gap bound is obtained directly from the two checked rejection-count
inequalities. The finite graph's size is linear in the old vertices and darts,
with an explicit coefficient determined only by the old alphabet cardinality.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

abbrev OutputVertex (V E A : Type*) :=
  QueryIncidence.Vertex (AlphabetGraph.Event E A) (AlphabetGraph.Address V E A)

abbrev OutputDart (E A : Type*) := QueryIncidence.Dart (AlphabetGraph.Event E A) 6

/-- The number of local verifier events for an alphabet with `q` symbols. -/
def localEventFactor (q : Nat) : Nat :=
  4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5

def vertexFactor (q : Nat) : Nat := localEventFactor q + 2 ^ (q * q)

def dartFactor (q : Nat) : Nat := 12 * localEventFactor q

def sizeFactor (q : Nat) : Nat := 2 ^ q + vertexFactor q + dartFactor q

theorem sizeFactor_positive (q : Nat) : 0 < sizeFactor q := by
  have hp : (0 : Nat) < 2 ^ q := pow_pos (by decide) q
  unfold sizeFactor
  omega

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Real gaps transfer without rational approximation, including an empty
old dart type. The loss is exactly `2048 * 6 = 12288`. -/
theorem gap_transfer_real [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : ConstraintGraph V E A) (eps : ℝ) (_eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : V → A,
      eps * (Fintype.card E : ℝ) ≤ (G.rejectionCount labeling : ℝ))
    (labeling : OutputVertex V E A → QueryIncidence.Label 6) :
    (eps / 12288) * (Fintype.card (OutputDart E A) : ℝ) ≤
      ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
  let assignment := QueryIncidence.decodedAssignment (by decide : 0 < 6) labeling
  have htest :
      (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    exact_mod_cast AlphabetGraph.rejection_count_bound G assignment
  have hinc :
      2 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) ≤
        ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
    exact_mod_cast QueryIncidence.rejection_count_bound
      (AlphabetGraph.verifier G) (by decide : 0 < 6) labeling
  have hscaled :
      eps * (Fintype.card E : ℝ) * (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    calc
      _ = (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (eps * (Fintype.card E : ℝ)) := by ring
      _ ≤ (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) :=
        mul_le_mul_of_nonneg_left (source (AlphabetGraph.decodedLabeling assignment))
          (Nat.cast_nonneg _)
      _ ≤ _ := htest
  change (eps / 12288) *
    (Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event E A) 6) : ℝ) ≤ _
  rw [QueryIncidence.card_dart, AlphabetGraph.card_event]
  push_cast
  nlinarith


variable [Fintype V] [Fintype E]

omit [Nonempty A] in
theorem card_output_vertex :
    Fintype.card (OutputVertex V E A) =
      Fintype.card V * 2 ^ Fintype.card A +
        Fintype.card E * vertexFactor (Fintype.card A) := by
  rw [QueryIncidence.card_vertex, AlphabetGraph.card_event,
    AlphabetGraph.card_address, AlphabetGraph.card_localEvent]
  unfold vertexFactor localEventFactor
  ring

omit [Nonempty A] in
theorem card_output_dart :
    Fintype.card (OutputDart E A) = Fintype.card E * dartFactor (Fintype.card A) := by
  rw [QueryIncidence.card_dart, AlphabetGraph.card_event, AlphabetGraph.card_localEvent]
  unfold dartFactor localEventFactor
  ring

omit [Nonempty A] in
theorem card_output_total :
    Fintype.card (OutputVertex V E A) + Fintype.card (OutputDart E A) =
      Fintype.card V * 2 ^ Fintype.card A +
        Fintype.card E * (vertexFactor (Fintype.card A) + dartFactor (Fintype.card A)) := by
  rw [card_output_vertex, card_output_dart]
  ring

omit [Nonempty A] in
/-- One coefficient depending only on the alphabet bounds the actual total
number of output vertices and darts. -/
theorem card_output_total_le :
    Fintype.card (OutputVertex V E A) + Fintype.card (OutputDart E A) ≤
      sizeFactor (Fintype.card A) * (Fintype.card V + Fintype.card E) := by
  rw [card_output_total]
  have hv : 2 ^ Fintype.card A ≤ sizeFactor (Fintype.card A) := by
    unfold sizeFactor
    omega
  have he : vertexFactor (Fintype.card A) + dartFactor (Fintype.card A) ≤
      sizeFactor (Fintype.card A) := by
    unfold sizeFactor
    exact Nat.add_le_add_right (Nat.le_add_left _ _) _
  calc
    _ ≤ Fintype.card V * sizeFactor (Fintype.card A) +
        Fintype.card E * sizeFactor (Fintype.card A) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hv) (Nat.mul_le_mul_left _ he)
    _ = _ := by ring

omit [Nonempty A] in
theorem card_output_vertex_le :
    Fintype.card (OutputVertex V E A) ≤
      sizeFactor (Fintype.card A) * (Fintype.card V + Fintype.card E) :=
  (Nat.le_add_right _ _).trans card_output_total_le

omit [Nonempty A] in
theorem card_output_dart_le :
    Fintype.card (OutputDart E A) ≤
      sizeFactor (Fintype.card A) * (Fintype.card V + Fintype.card E) :=
  (Nat.le_add_left _ _).trans card_output_total_le


end MaxCutGames.Foundations.PCP.AlphabetGraphBounds



namespace MaxCutGames.Foundations.PCP.AlphabetTableBounds

open AlphabetTable

variable {q : Nat}

/-- The actual table output obeys the real gap bound, with no rational
approximation and with empty input dart sets allowed. -/
theorem gap_transfer_real (hq : 0 < q) (input : GenericGraphTables.Table q)
    (eps : ℝ) (eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : Fin input.vertices → Fin q,
      eps * (input.darts : ℝ) ≤
        ((GenericGraphTables.semantics input).rejectionCount labeling : ℝ))
    (labeling : Fin (Table.build input).vertices → GraphTables.Label) :
    (eps / 12288) * ((Table.build input).darts : ℝ) ≤
      ((GraphTables.semantics (Table.build input)).rejectionCount labeling : ℝ) := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let lifted := fun vertex => Enumeration.labelEquiv.symm
    (labeling (Enumeration.vertexEquiv input.vertices input.darts q vertex))
  have h := AlphabetGraphBounds.gap_transfer_real
    (GenericGraphTables.semantics input) eps eps_nonnegative
    (by simpa only [Fintype.card_fin] using source) lifted
  rw [Enumeration.card_dart] at h
  have counts := Table.rejectionCount_build input lifted
  have restored : (fun v : Fin (Table.build input).vertices => Enumeration.labelEquiv
      (lifted ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) = labeling := by
    funext v
    dsimp only [lifted]
    rw [Enumeration.labelEquiv.apply_symm_apply]
    exact congrArg labeling
      ((Enumeration.vertexEquiv input.vertices input.darts q).apply_symm_apply v)
  rw [restored] at counts
  rw [← counts] at h
  exact h

/-- Exact output vertex count; this arithmetic identity also permits `q = 0`. -/
theorem build_vertices (input : GenericGraphTables.Table q) :
    (Table.build input).vertices = input.vertices * 2 ^ q +
      input.darts * AlphabetGraphBounds.vertexFactor q := by
  rw [Table.build_vertices]
  simp only [Enumeration.vertexCount, Enumeration.eventCount, Enumeration.addressCount,
    Enumeration.localCount, Enumeration.tapeCount, Enumeration.pairTapeCount,
    Enumeration.fiveTapeCount, AlphabetGraphBounds.vertexFactor,
    AlphabetGraphBounds.localEventFactor]
  ring

/-- Exact output dart count, including orientation and query multiplicity. -/
theorem build_darts (input : GenericGraphTables.Table q) :
    (Table.build input).darts = input.darts * AlphabetGraphBounds.dartFactor q := by
  rw [Table.build_darts]
  simp only [Enumeration.dartCount, Enumeration.eventCount, Enumeration.localCount,
    Enumeration.tapeCount, Enumeration.pairTapeCount, Enumeration.fiveTapeCount,
    AlphabetGraphBounds.dartFactor, AlphabetGraphBounds.localEventFactor]
  ring

theorem build_total (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts =
      input.vertices * 2 ^ q + input.darts *
        (AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q) := by
  rw [build_vertices, build_darts]
  ring

/-- A fixed alphabet gives one linear bound on the actual output table size. -/
theorem build_total_le (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) := by
  rw [build_total]
  have hv : 2 ^ q ≤ AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    omega
  have he : AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q ≤
      AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    exact Nat.add_le_add_right (Nat.le_add_left _ _) _
  calc
    _ ≤ input.vertices * AlphabetGraphBounds.sizeFactor q +
        input.darts * AlphabetGraphBounds.sizeFactor q :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hv) (Nat.mul_le_mul_left _ he)
    _ = _ := by ring

theorem build_vertices_le (input : GenericGraphTables.Table q) :
    (Table.build input).vertices ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) :=
  (Nat.le_add_right _ _).trans (build_total_le input)

theorem build_darts_le (input : GenericGraphTables.Table q) :
    (Table.build input).darts ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) :=
  (Nat.le_add_left _ _).trans (build_total_le input)

theorem sizeFactor_positive : 0 < AlphabetGraphBounds.sizeFactor q :=
  AlphabetGraphBounds.sizeFactor_positive q

end MaxCutGames.Foundations.PCP.AlphabetTableBounds

end OAI
