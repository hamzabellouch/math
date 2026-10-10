import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.GraphTables
import OAI.Combinatorics.IndependentSets.PCP.Minimum
import OAI.Combinatorics.IndependentSets.PCP.AlphabetRetraction
import OAI.Combinatorics.IndependentSets.Encoding.BinaryCoordinates

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialTables

open Target GraphTables

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by fin_cases i; rfl

def slotOrder : Slot ≃ Fin 3 where
  toFun
    | .first => 0
    | .second => 1
    | .third => 2
  invFun i := if i = 0 then .first else if i = 1 then .second else .third
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

def binaryOrder (n : Nat) : (Fin n → Bool) ≃ Fin (2 ^ n) where
  toFun bits := (IndependentSetsGames.Integration.BinaryCoordinates.pack bits).toFin
  invFun index := IndependentSetsGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index)
  left_inv bits := IndependentSetsGames.Integration.BinaryCoordinates.unpack_pack bits
  right_inv index := by
    change (IndependentSetsGames.Integration.BinaryCoordinates.pack
      (IndependentSetsGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index))).toFin = index
    rw [IndependentSetsGames.Integration.BinaryCoordinates.pack_unpack]

def labelOrder : AlphabetRetraction.Label64 ≃ GraphTables.Label := binaryOrder 6

def vertexOrder (F : Formula) :
    InitialGraph.Vertex F ≃ Fin (F.«variables» + F.clauses.length + 1) :=
  ((finSumFinEquiv.sumCongr unitOrder).trans finSumFinEquiv)

def eventOrder (F : Formula) : RandomEvent F ≃ Fin (F.clauses.length * 3) :=
  ((Equiv.refl (Fin F.clauses.length)).prodCongr slotOrder).trans finProdFinEquiv

def dartOrder (F : Formula) : InitialGraph.Dart F ≃ Fin (6 * F.clauses.length + 1) :=
  (((((eventOrder F).prodCongr finTwoEquiv.symm).trans finProdFinEquiv).sumCongr
    unitOrder).trans finSumFinEquiv).trans (finCongr (by omega))

def raw64 (F : Formula) : ConstraintGraph (InitialGraph.Vertex F)
    (InitialGraph.Dart F) AlphabetRetraction.Label64 :=
  AlphabetRetraction.pullback (InitialGraph.raw F) AlphabetRetraction.decode64

def table (F : Formula) : GraphTables.Table :=
  GraphTables.ofEnumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder

@[simp] theorem table_vertices (F : Formula) :
    (table F).vertices = F.«variables» + F.clauses.length + 1 := rfl

@[simp] theorem table_darts (F : Formula) : (table F).darts = 6 * F.clauses.length + 1 := rfl

theorem table_vertices_positive (F : Formula) : 0 < (table F).vertices := by
  rw [table_vertices]; omega

theorem table_darts_positive (F : Formula) : 0 < (table F).darts := by
  rw [table_darts]; omega

theorem raw64_satisfiable_iff (F : Formula) : (raw64 F).Satisfiable ↔ F.Satisfiable :=
  (AlphabetRetraction.satisfiable_pullback_iff (InitialGraph.raw F)
    AlphabetRetraction.decode64 AlphabetRetraction.encode64
      AlphabetRetraction.decode_encode64).trans (InitialGraph.raw_satisfiable_iff F)

theorem table_semantics (F : Formula) :
    GraphTables.semantics (table F) =
      (raw64 F).reindex (vertexOrder F) (dartOrder F) labelOrder := by
  change GraphTables.semantics (GraphTables.ofGraph
    (GraphTables.enumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder)) = _
  rw [GraphTables.semantics_ofGraph]
  rfl

theorem table_satisfiable_iff (F : Formula) :
    (GraphTables.semantics (table F)).Satisfiable ↔ F.Satisfiable := by
  rw [table_semantics]
  exact ((raw64 F).satisfiable_reindex (vertexOrder F) (dartOrder F) labelOrder).trans
    (raw64_satisfiable_iff F)

theorem initial_rejection (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : Fin (table F).vertices → GraphTables.Label) :
    1 ≤ (GraphTables.semantics (table F)).rejectionCount labeling :=
  ConstraintGraph.rejectionCount_positive _
    (fun h => unsat ((table_satisfiable_iff F).mp h)) labeling

theorem initial_size (F : Formula) :
    (table F).vertices + (table F).darts = F.«variables» + 7 * F.clauses.length + 2 := by
  rw [table_vertices, table_darts]
  omega

end IndependentSetsGames.Foundations.PCP.RawInitialTables
noncomputable section

namespace IndependentSetsGames.Foundations.PCP.FiniteGraph

structure Bundle (A : Type) where
  Vertex : Type
  Dart : Type
  vertexFintype : Fintype Vertex
  dartFintype : Fintype Dart
  vertexDecidableEq : DecidableEq Vertex
  dartDecidableEq : DecidableEq Dart
  dartNonempty : Nonempty Dart
  graph : ConstraintGraph Vertex Dart A

namespace Bundle

variable {A : Type}

instance instFintypeVertex (G : Bundle A) : Fintype G.Vertex := G.vertexFintype
instance instFintypeDart (G : Bundle A) : Fintype G.Dart := G.dartFintype
instance instDecidableEqVertex (G : Bundle A) : DecidableEq G.Vertex := G.vertexDecidableEq
instance instDecidableEqDart (G : Bundle A) : DecidableEq G.Dart := G.dartDecidableEq
instance instNonemptyDart (G : Bundle A) : Nonempty G.Dart := G.dartNonempty

instance instNonemptyVertex (G : Bundle A) : Nonempty G.Vertex := by
  obtain ⟨d⟩ := G.dartNonempty
  exact ⟨G.graph.tail d⟩

def ofGraph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) : Bundle A where
  Vertex := V
  Dart := E
  vertexFintype := inferInstance
  dartFintype := inferInstance
  vertexDecidableEq := inferInstance
  dartDecidableEq := inferInstance
  dartNonempty := inferInstance
  graph := G

def size (G : Bundle A) : Nat := Fintype.card G.Vertex + Fintype.card G.Dart

def Satisfiable (G : Bundle A) : Prop := G.graph.Satisfiable

def rejectionCount (G : Bundle A) (labeling : G.Vertex → A) : Nat :=
  G.graph.rejectionCount labeling

theorem size_positive (G : Bundle A) : 0 < G.size :=
  lt_of_lt_of_le (Fintype.card_pos : 0 < Fintype.card G.Dart) (Nat.le_add_left _ _)

theorem dartCard_le_size (G : Bundle A) : Fintype.card G.Dart ≤ G.size :=
  Nat.le_add_left _ _

@[simp] theorem ofGraph_graph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).graph = G := rfl

@[simp] theorem ofGraph_size {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).size = Fintype.card V + Fintype.card E := rfl

@[simp] theorem ofGraph_satisfiable {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).Satisfiable ↔ G.Satisfiable := Iff.rfl

@[simp] theorem ofGraph_rejectionCount {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) (labeling : V → A) :
    (ofGraph G).rejectionCount labeling = G.rejectionCount labeling := rfl

end Bundle
end IndependentSetsGames.Foundations.PCP.FiniteGraph
end

end OAI
