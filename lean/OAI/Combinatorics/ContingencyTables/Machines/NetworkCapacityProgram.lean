import OAI.Combinatorics.ContingencyTables.Transport.NetworkVertexCode
import OAI.Combinatorics.ContingencyTables.Machines.FlowLoopProgram

namespace OAI

/-! # Constructing the bounded-table capacity network in binary -/

namespace ContingencyTables.NetworkCapacityProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode ResidualGraphProgram

abbrev EntryInput := Input×(ℕ×ℕ)

def kindRealizer : Realizer (fun z : ℕ×ℕ=>kind z.1 z.2) :=
  (choose (composition (pair second (constant 0)) natEqual) (constant 0)
    (choose (composition (pair second (constant 1)) natEqual) (constant 1)
      (choose (composition (pair second (composition (pair (constant 2) first) add)) less)
        (constant 2) (constant 3)))).congr (by
          intro z
          simp only [Function.comp_apply,kind,decide_eq_true_eq])

lemma polynomial_kind : PolynomialTime kindRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 0))
      polynomial_natEqual) (polynomial_constant 0)
    (polynomial_choose
      (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 1))
        polynomial_natEqual) (polynomial_constant 1)
      (polynomial_choose
        (polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_first)
            polynomial_add)) polynomial_less)
        (polynomial_constant 2) (polynomial_constant 3))))

def rowCount (z : EntryInput) : ℕ := z.1.1.1.length

def rowCountRealizer : Realizer rowCount :=
  composition (composition (composition first first) first) listLength

lemma polynomial_rowCount : PolynomialTime rowCountRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_listLength

def columnBase (z : EntryInput) : ℕ := 2+rowCount z

def columnBaseRealizer : Realizer columnBase :=
  composition (f := fun z : EntryInput=>(2,rowCount z))
    (g := fun a : ℕ×ℕ=>a.1+a.2) (pair (constant 2) rowCountRealizer) add

lemma polynomial_columnBase : PolynomialTime columnBaseRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_rowCount)
    polynomial_add

def kinds (z : EntryInput) : ℕ×ℕ :=
  (kind (rowCount z) z.2.1,kind (rowCount z) z.2.2)

def kindsRealizer : Realizer kinds :=
  pair (composition (pair rowCountRealizer (composition second first)) kindRealizer)
    (composition (pair rowCountRealizer (composition second second)) kindRealizer)

lemma polynomial_kinds : PolynomialTime kindsRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair polynomial_rowCount
    (polynomial_composition polynomial_second polynomial_first)) polynomial_kind)
    (polynomial_composition (polynomial_pair polynomial_rowCount
      (polynomial_composition polynomial_second polynomial_second)) polynomial_kind)

def pattern (a b : ℕ) (z : EntryInput) : Bool :=
  decide ((kinds z).1=a) && decide ((kinds z).2=b)

def patternRealizer (a b : ℕ) : Realizer (pattern a b) :=
  composition kindsRealizer (composition (pair
    (composition (pair first (constant a)) natEqual)
    (composition (pair second (constant b)) natEqual)) boolAnd)

lemma polynomial_pattern (a b : ℕ) : PolynomialTime (patternRealizer a b) :=
  polynomial_composition polynomial_kinds (polynomial_composition
    (polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_first (polynomial_constant a))
        polynomial_natEqual)
      (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant b))
        polynomial_natEqual)) polynomial_boolAnd)

def rowRead (z : EntryInput) : ℕ := z.1.1.1.getD (z.2.2-2) 0

def rowReadRealizer : Realizer rowRead :=
  composition (pair (composition (composition first first) first)
    (composition (pair (composition second second) (constant 2)) subtract)) (getDFast 0)

lemma polynomial_rowRead : PolynomialTime rowReadRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_second) (polynomial_constant 2))
      polynomial_subtract)) (polynomial_getDFast 0)

def columnRead (z : EntryInput) : ℕ := z.1.1.2.getD (z.2.1-columnBase z) 0

def columnReadRealizer : Realizer columnRead :=
  composition (pair (composition (composition first first) second)
    (composition (pair (composition second first) columnBaseRealizer) subtract)) (getDFast 0)

lemma polynomial_columnRead : PolynomialTime columnReadRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_first) polynomial_columnBase)
      polynomial_subtract)) (polynomial_getDFast 0)

def boundRead (z : EntryInput) : ℕ :=
  capacityEntry (z.1.2,(z.2.1-2,z.2.2-columnBase z))

def boundReadRealizer : Realizer boundRead :=
  composition (pair (composition first second)
    (pair (composition (pair (composition second first) (constant 2)) subtract)
      (composition (pair (composition second second) columnBaseRealizer) subtract)))
    capacityEntryRealizer

lemma polynomial_boundRead : PolynomialTime boundReadRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_first) (polynomial_constant 2))
        polynomial_subtract)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_second) polynomial_columnBase)
        polynomial_subtract))) polynomial_capacityEntry

def entryRealizer : Realizer entry :=
  (choose (patternRealizer 0 2) rowReadRealizer
    (choose (patternRealizer 2 3) boundReadRealizer
      (choose (patternRealizer 3 1) columnReadRealizer (constant 0)))).congr (by
        intro z
        have hp (a b : ℕ) : pattern a b z=true ↔
            kind z.1.1.1.length z.2.1=a ∧ kind z.1.1.1.length z.2.2=b := by
          change ((decide (kind z.1.1.1.length z.2.1=a)) &&
            (decide (kind z.1.1.1.length z.2.2=b)))=true ↔ _
          rw [Bool.and_eq_true]
          constructor
          · rintro ⟨ha,hb⟩
            exact ⟨_root_.of_decide_eq_true ha,_root_.of_decide_eq_true hb⟩
          · rintro ⟨ha,hb⟩
            exact ⟨_root_.decide_eq_true ha,_root_.decide_eq_true hb⟩
        simp only [hp,columnBase,rowRead,columnRead,boundRead,entry,rowCount])

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_congr _ (polynomial_choose (polynomial_pattern 0 2) polynomial_rowRead
    (polynomial_choose (polynomial_pattern 2 3) polynomial_boundRead
      (polynomial_choose (polynomial_pattern 3 1) polynomial_columnRead (polynomial_constant 0))))

def vertexCountRealizer : Realizer vertexCount :=
  composition (f := fun z : Input=>(2,z.1.1.length+z.1.2.length))
    (g := fun a : ℕ×ℕ=>a.1+a.2)
    (pair (constant 2) (composition
      (f := fun z : Input=>(z.1.1.length,z.1.2.length))
      (g := fun a : ℕ×ℕ=>a.1+a.2)
      (pair (composition (composition first first) listLength)
        (composition (composition first second) listLength)) add)) add

lemma polynomial_vertexCount : PolynomialTime vertexCountRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 2)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_listLength)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_listLength)) polynomial_add)) polynomial_add

def vertices (z : Input) : List ℕ := List.range (vertexCount z)
def verticesRealizer : Realizer vertices := composition vertexCountRealizer range

lemma polynomial_vertices : PolynomialTime verticesRealizer := by
  apply polynomial_boundedRange polynomial_vertexCount (2+2*X)
  intro z
  have hr := (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))
  have hc := (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))
  simp only [vertexCount,eval_add,eval_ofNat,eval_mul,eval_X]
  omega

def row (z : Input×ℕ) : List ℕ :=
  (vertices z.1).map (fun v=>entry (z.1,(z.2,v)))

def rowRealizer : Realizer row :=
  composition (pair identity (composition first verticesRealizer))
    (mapWith (composition
      (pair (composition first first) (pair (composition first second) second)) entryRealizer))

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_vertices))
    (polynomial_mapWith (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_entry))

def matrixRealizer : Realizer matrix :=
  composition (pair identity verticesRealizer) (mapWith rowRealizer)

lemma polynomial_matrix : PolynomialTime matrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_vertices)
    (polynomial_mapWith polynomial_row)

def solve (z : Input) : FlowMatrix := FlowLoopProgram.run (matrix z,(0,1))

def solveRealizer : Realizer solve :=
  composition (pair matrixRealizer (constant (0,1))) FlowLoopProgram.runRealizer

lemma polynomial_solve : PolynomialTime solveRealizer :=
  polynomial_composition (polynomial_pair polynomial_matrix (polynomial_constant (0,1)))
    FlowLoopProgram.polynomial_run

theorem solve_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    solve (data r c b)=flowCode (EdmondsKarpAlgorithm.maxFlow
      (BoundedTableFeasibility.networkCapacity r c b)
      (BoundedTableFeasibility.vertices m n LayeredTableNetwork.source)
      (BoundedTableFeasibility.vertices m n LayeredTableNetwork.sink)) := by
  have hs : (BoundedTableFeasibility.vertices m n (LayeredTableNetwork.source :
      LayeredTableNetwork.Vertex m n)).val=0 := index_vertices _
  have ht : (BoundedTableFeasibility.vertices m n (LayeredTableNetwork.sink :
      LayeredTableNetwork.Vertex m n)).val=1 := index_vertices _
  unfold solve
  rw [matrix_code]
  simpa only [hs,ht] using FlowLoopProgram.run_code
    (BoundedTableFeasibility.networkCapacity r c b)
    (BoundedTableFeasibility.vertices m n LayeredTableNetwork.source)
    (BoundedTableFeasibility.vertices m n LayeredTableNetwork.sink)
    BoundedTableFeasibility.source_ne_sink

end ContingencyTables.NetworkCapacityProgram

end OAI
