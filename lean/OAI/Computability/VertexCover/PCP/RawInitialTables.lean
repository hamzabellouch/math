import Mathlib
import OAI.Computability.VertexCover.PCP.AlphabetRetraction
import OAI.Computability.VertexCover.PCP.BinaryCoordinates
import OAI.Computability.VertexCover.PCP.GraphGap

namespace OAI

                                                                                         

namespace UniqueGames.Foundations.PCP.RawInitialTables

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
  toFun bits := (UniqueGames.Integration.BinaryCoordinates.pack bits).toFin
  invFun index := UniqueGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index)
  left_inv bits := UniqueGames.Integration.BinaryCoordinates.unpack_pack bits
  right_inv index := by
    change (UniqueGames.Integration.BinaryCoordinates.pack
      (UniqueGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index))).toFin = index
    rw [UniqueGames.Integration.BinaryCoordinates.pack_unpack]

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

end UniqueGames.Foundations.PCP.RawInitialTables

end OAI
