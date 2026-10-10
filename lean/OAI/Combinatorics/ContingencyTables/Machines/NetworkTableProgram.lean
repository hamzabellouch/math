import OAI.Combinatorics.ContingencyTables.Machines.NetworkFeasibilityProgram

namespace OAI

/-! # Extracting the bounded table from the executed flow

The output reads the row-to-column arcs of the computed flow. Both the
matrix dimensions and the encoded entries are obtained from the input;
there is no choice of a mathematical witness in the program.
-/

namespace ContingencyTables.NetworkTableProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode ResidualGraphProgram
open scoped BigOperators

abbrev Prepared := (List ℕ×List ℕ)×FlowMatrix
abbrev CellInput := Prepared×(ℕ×ℕ)

def cell (z : CellInput) : ℕ :=
  let a := flowEntry (z.1.2,(2+z.2.1,2+z.1.1.1.length+z.2.2))
  a.1-a.2

def cellRealizer : Realizer cell := by
  let F : Realizer (fun z : CellInput=>z.1.2) := composition first second
  let I : Realizer (fun z : CellInput=>2+z.2.1) :=
    composition (f := fun z : CellInput=>(2,z.2.1))
      (g := fun a : ℕ×ℕ=>a.1+a.2) (pair (constant 2) (composition second first)) add
  let J : Realizer (fun z : CellInput=>2+z.1.1.1.length+z.2.2) :=
    composition (f := fun z : CellInput=>(2+z.1.1.1.length,z.2.2))
      (g := fun a : ℕ×ℕ=>a.1+a.2)
      (pair (composition (f := fun z : CellInput=>(2,z.1.1.1.length))
        (g := fun a : ℕ×ℕ=>a.1+a.2)
        (pair (constant 2) (composition (composition (composition first first) first) listLength)) add)
        (composition second second)) add
  exact composition (f := fun z : CellInput=>
    flowEntry (z.1.2,(2+z.2.1,2+z.1.1.1.length+z.2.2)))
    (g := fun a : SignedPairProgram.Signed=>a.1-a.2)
    (composition (f := fun z : CellInput=>
      (z.1.2,(2+z.2.1,2+z.1.1.1.length+z.2.2))) (g := flowEntry)
      (pair F (pair I J)) flowEntryRealizer) subtract

lemma polynomial_cell : PolynomialTime cellRealizer := by
  unfold cellRealizer
  apply polynomial_composition
  · apply polynomial_composition
    · exact polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        (polynomial_pair
          (polynomial_composition (polynomial_pair (polynomial_constant 2)
            (polynomial_composition polynomial_second polynomial_first)) polynomial_add)
          (polynomial_composition (polynomial_pair
            (polynomial_composition (polynomial_pair (polynomial_constant 2)
              (polynomial_composition
                (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
                  polynomial_first) polynomial_listLength)) polynomial_add)
            (polynomial_composition polynomial_second polynomial_second)) polynomial_add))
    · exact polynomial_flowEntry
  · exact polynomial_subtract

def rowIndices (z : Prepared) : List ℕ := List.range z.1.1.length
def columnIndices (z : Prepared) : List ℕ := List.range z.1.2.length

def rowIndicesRealizer : Realizer rowIndices :=
  composition (composition (composition first first) listLength) range

def columnIndicesRealizer : Realizer columnIndices :=
  composition (composition (composition first second) listLength) range

lemma polynomial_rowIndices : PolynomialTime rowIndicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma polynomial_columnIndices : PolynomialTime columnIndicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))

def row (z : Prepared×ℕ) : List ℕ :=
  (columnIndices z.1).map (fun j=>cell (z.1,(z.2,j)))

def rowRealizer : Realizer row :=
  composition (pair identity (composition first columnIndicesRealizer))
    (mapWith (composition (f := fun z : (Prepared×ℕ)×ℕ=>(z.1.1,(z.1.2,z.2)))
      (g := cell) (pair (composition first first)
        (pair (composition first second) second)) cellRealizer))

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_columnIndices))
    (polynomial_mapWith (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_cell))

def table (z : Prepared) : NatMatrix :=
  (rowIndices z).map (fun i=>row (z,i))

def tableRealizer : Realizer table :=
  composition (pair identity rowIndicesRealizer) (mapWith rowRealizer)

lemma polynomial_table : PolynomialTime tableRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_rowIndices)
    (polynomial_mapWith polynomial_row)

def prepare (z : Input) : Prepared :=
  (z.1,NetworkCapacityProgram.solve z)

def prepareRealizer : Realizer prepare :=
  pair first NetworkCapacityProgram.solveRealizer

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair polynomial_first NetworkCapacityProgram.polynomial_solve

def output (z : Input) : NatMatrix := table (prepare z)
def outputRealizer : Realizer output := composition prepareRealizer tableRealizer
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare polynomial_table

private lemma signedParts_toNat (z : ℤ) :
    (ForestAffineProgram.signedParts z).1-(ForestAffineProgram.signedParts z).2=z.toNat := by
  cases z <;> simp [ForestAffineProgram.signedParts]

lemma cell_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) :
    cell (prepare (data r c b),(i.val,j.val))=
      LayeredTableNetwork.decode (BoundedTableFeasibility.computedFlow r c b) i j := by
  let f := EdmondsKarpAlgorithm.maxFlow (BoundedTableFeasibility.networkCapacity r c b)
    (BoundedTableFeasibility.vertices m n LayeredTableNetwork.source)
    (BoundedTableFeasibility.vertices m n LayeredTableNetwork.sink)
  have he := flowEntry_code f
    (BoundedTableFeasibility.vertices m n (LayeredTableNetwork.row i))
    (BoundedTableFeasibility.vertices m n (LayeredTableNetwork.column j))
  simp only [index_vertices,LayeredTableNetwork.row,LayeredTableNetwork.column,index] at he
  have hlen : (data r c b).1.1.length=m := by simp only [data,List.length_ofFn]
  dsimp only [cell,prepare]
  rw [hlen,NetworkCapacityProgram.solve_code,he]
  change (ForestAffineProgram.signedParts (f _ _)).1-
    (ForestAffineProgram.signedParts (f _ _)).2=(f _ _).toNat
  exact signedParts_toNat _

lemma output_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    output (data r c b)=natCode
      (LayeredTableNetwork.decode (BoundedTableFeasibility.computedFlow r c b)) := by
  simp only [output,table,row,rowIndices,columnIndices,prepare,data,List.length_ofFn,
    DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn,natCode]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  exact cell_code r c b i j

/-- The computed list output encodes a table with the supplied margins and
bounds whenever the concrete feasibility test accepts. -/
theorem output_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (ht : NetworkFeasibilityProgram.test (data r c b)=true) :
    ∃ X, output (data r c b)=natCode X ∧ HasMargins X r c ∧ ∀ i j,X i j≤b i j := by
  have hp : (∑ i,r i)=∑ j,c j ∧
      LayeredTableNetwork.value (BoundedTableFeasibility.computedFlow r c b)=∑ i,(r i:ℤ) := by
    simpa only [NetworkFeasibilityProgram.test_eq_feasible,
      BoundedTableFeasibility.feasibleTest,decide_eq_true_eq] using ht
  exact ⟨_,output_code r c b,LayeredTableNetwork.decode_boundedTable r c b _
    (BoundedTableFeasibility.computedFlow_feasible hEK r c b) hp.2 hp.1⟩

end ContingencyTables.NetworkTableProgram

end OAI
