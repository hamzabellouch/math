import Mathlib
import OAI.Computability.VertexCover.PCP.GenericGraphTables
import OAI.Computability.VertexCover.PCP.AlphabetTableEnumeration
import OAI.Computability.VertexCover.PCP.AlphabetTableRelations

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

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

theorem rows_reverseIndex (input : GenericGraphTables.Table q)
    (index : Fin (Enumeration.dartCount input.darts q)) :
    (rows input)[index].reverseIndex =
      Enumeration.dartEquiv input.darts q
        (((Enumeration.dartEquiv input.darts q).symm index).1,
          !((Enumeration.dartEquiv input.darts q).symm index).2) := by
  simp [rows, rowFromDart]

private theorem dartRow_ext {n m : Nat} {left right : GraphTables.DartRow n m}
    (ht : left.tail = right.tail) (hr : left.reverseIndex = right.reverseIndex)
    (hp : left.relation = right.relation) : left = right := by
  cases left
  cases right
  cases ht
  cases hr
  cases hp
  rfl

private theorem relation_ext {left right : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt left a b = GraphTables.relationAt right a b) :
    left = right := by
  apply Vector.ext
  intro i hi
  let labels := GraphTables.relationIndex.symm (⟨i, hi⟩ : Fin 4096)
  have index : GraphTables.relationIndex labels = (⟨i, hi⟩ : Fin 4096) :=
    GraphTables.relationIndex.apply_symm_apply _
  have point := h labels.1 labels.2
  simpa only [GraphTables.relationAt, index, Fin.getElem_fin] using point

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
  apply dartRow_ext
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
  · apply relation_ext
    intro a b
    rw [GraphTables.relationAt_relationOf]
    have relation := Relations.relationAt_relation_graph (GenericGraphTables.semantics input)
      edge event slot orientation a b
    have predicate : (GenericGraphTables.semantics input).accepts edge =
        Relations.oldPredicate input.rows[edge].relation := rfl
    rw [predicate] at relation
    simp only [rowFromDart, Relations.relationFromTable,
      GenericGraphTables.semantics_tail, ConstraintGraph.head,
      GenericGraphTables.semantics_reverse] at relation ⊢
    exact relation

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

def build (input : GenericGraphTables.Table q) : GraphTables.Table where
  vertices := Enumeration.vertexCount input.vertices input.darts q
  darts := Enumeration.dartCount input.darts q
  rows := rows input
  valid := rows_valid input

@[simp] theorem build_vertices (input : GenericGraphTables.Table q) :
    (build input).vertices = Enumeration.vertexCount input.vertices input.darts q := rfl

@[simp] theorem build_darts (input : GenericGraphTables.Table q) :
    (build input).darts = Enumeration.dartCount input.darts q := rfl

private theorem table_rows_congr {n m : Nat} {left right : GraphTables.Rows n m}
    (h : left = right) (hl : GraphTables.Valid left) (hr : GraphTables.Valid right) :
    (⟨n, m, left, hl⟩ : GraphTables.Table) = ⟨n, m, right, hr⟩ := by
  subst right
  rfl

private theorem semantics_rows_congr {n m : Nat} {left right : GraphTables.Rows n m}
    (h : left = right) (hl : GraphTables.Valid left) (hr : GraphTables.Valid right) :
    GraphTables.semantics (⟨n, m, left, hl⟩ : GraphTables.Table) =
      GraphTables.semantics (⟨n, m, right, hr⟩ : GraphTables.Table) := by
  subst right
  rfl

theorem build_eq_ofEnumeratedGraph (input : GenericGraphTables.Table q) :
    build input =
      GraphTables.ofEnumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv := by
  exact table_rows_congr (rows_eq_graphRows input) (rows_valid input)
    (GraphTables.graphRows_valid _)

theorem semantics_build (input : GenericGraphTables.Table q) :
    GraphTables.semantics (build input) =
      GraphTables.enumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv := by
  exact (semantics_rows_congr (rows_eq_graphRows input) (rows_valid input)
    (GraphTables.graphRows_valid _)).trans (GraphTables.semantics_ofGraph _)

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

theorem rowList_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.rowList (build input) =
      (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).map
        (rowFromDart input) := by
  change (Vector.ofFn (fun index => rowFromDart input
      ((Enumeration.dartEquiv input.darts q).symm index))).toList =
    (List.ofFn (Enumeration.dartEquiv input.darts q).symm).map (rowFromDart input)
  simp only [Vector.toList_ofFn, List.map_ofFn, Function.comp_def]

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

end UniqueGames.Foundations.PCP.AlphabetTable.Table

end OAI
