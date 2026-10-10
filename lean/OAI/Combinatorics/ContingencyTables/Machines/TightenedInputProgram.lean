import OAI.Combinatorics.ContingencyTables.Machines.EndpointMatrixProgram
import OAI.Combinatorics.ContingencyTables.Transport.ComputedTableTightening
import OAI.Combinatorics.ContingencyTables.Machines.NetworkTableProgram

namespace OAI

/-! # Executed endpoint translation and a feasible tightened baseline

The lower and upper matrices are computed by the endpoint scans. Binary
subtraction updates the capacities and both margins, then the same proved
flow program produces a baseline table in the translated instance.
-/

namespace ContingencyTables.TightenedInputProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram NetworkVertexCode
open scoped BigOperators Classical

abbrev TranslationInput := Input×NatMatrix
abbrev MarginInput := TranslationInput×ℕ
abbrev CellInput := MarginInput×ℕ

def rowValue (z : MarginInput) : ℕ :=
  z.1.1.1.1.getD z.2 0-(z.1.1.2.getD z.2 []).sum
def rowValueRealizer : Realizer rowValue :=
  composition (pair
    (composition (pair (composition (composition (composition first first) first) first) second)
      (getDFast 0))
    (composition (composition (pair (composition (composition first first) second) second)
      (getDFast [])) listSum)) subtract
lemma polynomial_rowValue : PolynomialTime rowValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        polynomial_first polynomial_first) polynomial_first) polynomial_first)
      polynomial_second) (polynomial_getDFast 0))
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_second) (polynomial_getDFast [])) polynomial_listSum))
    polynomial_subtract

def columnValue (z : MarginInput) : ℕ :=
  z.1.1.1.2.getD z.2 0-(BoundedComplementProgram.columnValues (z.1.1,z.2)).sum
def columnValueRealizer : Realizer columnValue :=
  composition (pair
    (composition (pair (composition (composition (composition first first) first) second) second)
      (getDFast 0))
    (composition (composition
      (pair (composition first first) second) BoundedComplementProgram.columnValuesRealizer)
      listSum)) subtract
lemma polynomial_columnValue : PolynomialTime columnValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_second) (polynomial_getDFast 0))
    (polynomial_composition (polynomial_composition
      (polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      BoundedComplementProgram.polynomial_columnValues) polynomial_listSum)) polynomial_subtract

def position (z : CellInput) : ℕ×ℕ := (z.1.2,z.2)
def positionRealizer : Realizer position := pair (composition first second) second
lemma polynomial_position : PolynomialTime positionRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second

def cellValue (z : CellInput) : ℕ :=
  capacityEntry (z.1.1.2,position z)-capacityEntry (z.1.1.1.2,position z)
def cellValueRealizer : Realizer cellValue :=
  composition (pair
    (composition (pair (composition (composition first first) second) positionRealizer)
      capacityEntryRealizer)
    (composition (pair (composition (composition (composition first first) first) second)
      positionRealizer) capacityEntryRealizer)) subtract
lemma polynomial_cellValue : PolynomialTime cellValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_position) polynomial_capacityEntry)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_position) polynomial_capacityEntry)) polynomial_subtract

def rowIndices (z : TranslationInput) : List ℕ := BoundedComplementProgram.rowIndices z.1
def rowIndicesRealizer : Realizer rowIndices :=
  composition first BoundedComplementProgram.rowIndicesRealizer
lemma polynomial_rowIndices : PolynomialTime rowIndicesRealizer :=
  polynomial_composition polynomial_first BoundedComplementProgram.polynomial_rowIndices

def columnIndices (z : TranslationInput) : List ℕ := BoundedComplementProgram.columnIndices z.1
def columnIndicesRealizer : Realizer columnIndices :=
  composition first BoundedComplementProgram.columnIndicesRealizer
lemma polynomial_columnIndices : PolynomialTime columnIndicesRealizer :=
  polynomial_composition polynomial_first BoundedComplementProgram.polynomial_columnIndices

def capacityRow (z : MarginInput) : List ℕ :=
  (columnIndices z.1).map (fun j=>cellValue (z,j))
def capacityRowRealizer : Realizer capacityRow :=
  composition (pair identity (composition first columnIndicesRealizer)) (mapWith cellValueRealizer)
lemma polynomial_capacityRow : PolynomialTime capacityRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_columnIndices))
    (polynomial_mapWith polynomial_cellValue)

def translate (z : TranslationInput) : Input :=
  (((rowIndices z).map (fun i=>rowValue (z,i)),
    (columnIndices z).map (fun j=>columnValue (z,j))),
    (rowIndices z).map (fun i=>capacityRow (z,i)))
def translateRealizer : Realizer translate :=
  pair (pair
    (composition (pair identity rowIndicesRealizer) (mapWith rowValueRealizer))
    (composition (pair identity columnIndicesRealizer) (mapWith columnValueRealizer)))
    (composition (pair identity rowIndicesRealizer) (mapWith capacityRowRealizer))
lemma polynomial_translate : PolynomialTime translateRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_rowIndices)
      (polynomial_mapWith polynomial_rowValue))
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_columnIndices)
      (polynomial_mapWith polynomial_columnValue)))
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_rowIndices)
      (polynomial_mapWith polynomial_capacityRow))

lemma rowValue_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (l u : Fin m→Fin n→ℕ) (i : Fin m) :
    rowValue ((data r c l,natCode u),i.val)=TableTightening.rows r l i := by
  simp only [rowValue,data,natCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,dite_true,Option.getD_some,Fin.eta,List.sum_ofFn,TableTightening.rows]

lemma columnValue_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (l u : Fin m→Fin n→ℕ) (j : Fin n) :
    columnValue ((data r c l,natCode u),j.val)=TableTightening.columns c l j := by
  simp only [columnValue,BoundedComplementProgram.columnValues,data,natCode,List.map_ofFn,
    Function.comp_def,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    j.isLt,dite_true,Option.getD_some,Fin.eta,List.sum_ofFn,TableTightening.columns]

lemma cellValue_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (l u : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) :
    cellValue (((data r c l,natCode u),i.val),j.val)=TableTightening.bounds l u i j := by
  change capacityEntry (natCode u,(i.val,j.val))-capacityEntry (natCode l,(i.val,j.val))=_
  rw [capacityEntry_code,capacityEntry_code]
  rfl

lemma translate_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (l u : Fin m→Fin n→ℕ) :
    translate (data r c l,natCode u)=data (TableTightening.rows r l)
      (TableTightening.columns c l) (TableTightening.bounds l u) := by
  unfold translate
  apply Prod.ext
  · apply Prod.ext
    · simp only [rowIndices,BoundedComplementProgram.rowIndices,data,List.length_ofFn,
        DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      exact rowValue_code r c l u i
    · simp only [columnIndices,BoundedComplementProgram.columnIndices,data,List.length_ofFn,
        DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn]
      apply congrArg List.ofFn
      funext j
      exact columnValue_code r c l u j
  · simp only [rowIndices,BoundedComplementProgram.rowIndices,data,List.length_ofFn,
      DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn,natCode]
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_apply]
    simp only [capacityRow,columnIndices,BoundedComplementProgram.columnIndices,List.length_ofFn,
      DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    exact cellValue_code r c l u i j

def prepare (z : Input) : TranslationInput :=
  ((z.1,EndpointMatrixProgram.lowerMatrix z),EndpointMatrixProgram.upperMatrix z)
def prepareRealizer : Realizer prepare :=
  pair (pair first EndpointMatrixProgram.lowerMatrixRealizer) EndpointMatrixProgram.upperMatrixRealizer
lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair polynomial_first EndpointMatrixProgram.polynomial_lowerMatrix)
    EndpointMatrixProgram.polynomial_upperMatrix

def compute (z : Input) : Input := translate (prepare z)
def computeRealizer : Realizer compute :=
  composition (f:=prepare) (g:=translate) prepareRealizer translateRealizer
lemma polynomial_compute : PolynomialTime computeRealizer :=
  polynomial_composition polynomial_prepare polynomial_translate

lemma compute_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    compute (data r c b)=data (ComputedTableTightening.newRows r c b)
      (ComputedTableTightening.newColumns r c b) (ComputedTableTightening.newBounds r c b) := by
  unfold compute prepare
  rw [EndpointMatrixProgram.lowerMatrix_code,EndpointMatrixProgram.upperMatrix_code]
  exact translate_code r c (ComputedTableTightening.lower r c b) (ComputedTableTightening.upper r c b)

def baseline (z : Input) : NatMatrix := NetworkTableProgram.output (compute z)
def baselineRealizer : Realizer baseline :=
  composition (f:=compute) (g:=NetworkTableProgram.output) computeRealizer NetworkTableProgram.outputRealizer
lemma polynomial_baseline : PolynomialTime baselineRealizer :=
  polynomial_composition polynomial_compute NetworkTableProgram.polynomial_output

/-- Endpoint translation preserves a concrete feasible witness. -/
theorem translated_nonempty {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) :
    ∃ Y,HasMargins Y (ComputedTableTightening.newRows r c b)
      (ComputedTableTightening.newColumns r c b) ∧
      ∀ i j,Y i j≤ComputedTableTightening.newBounds r c b i j := by
  obtain ⟨X,hX⟩ := hne
  let x : BoundedTable r c b := ⟨⟨X,hX.1⟩,hX.2⟩
  let y := ComputedTableTightening.tighten hEK r c b ⟨X,hX⟩ x
  exact ⟨y.val.val,y.val.property,y.property⟩

/-- The stored baseline comes from the executed flow decoder, with all
its margin and capacity obligations discharged by endpoint translation. -/
theorem baseline_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) :
    ∃ Y,baseline (data r c b)=natCode Y ∧
      HasMargins Y (ComputedTableTightening.newRows r c b)
        (ComputedTableTightening.newColumns r c b) ∧
      ∀ i j,Y i j≤ComputedTableTightening.newBounds r c b i j := by
  have ht := (NetworkFeasibilityProgram.test_correct hEK
    (ComputedTableTightening.newRows r c b)
    (ComputedTableTightening.newColumns r c b)
    (ComputedTableTightening.newBounds r c b)).mpr (translated_nonempty hEK r c b hne)
  have h := NetworkTableProgram.output_correct hEK
    (ComputedTableTightening.newRows r c b)
    (ComputedTableTightening.newColumns r c b)
    (ComputedTableTightening.newBounds r c b) ht
  simpa only [baseline,compute_code] using h

end ContingencyTables.TightenedInputProgram

end OAI
