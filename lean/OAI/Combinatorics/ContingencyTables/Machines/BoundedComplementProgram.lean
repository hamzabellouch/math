import OAI.Combinatorics.ContingencyTables.Transport.BoundedTableComplement
import OAI.Combinatorics.ContingencyTables.Machines.NetworkFeasibilityProgram

namespace OAI

/-! # Computing complementary bounded-table margins in binary -/

namespace ContingencyTables.BoundedComplementProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode

abbrev EntryInput := Input×ℕ

def rowValue (z : EntryInput) : ℕ :=
  (z.1.2.getD z.2 []).sum-z.1.1.1.getD z.2 0

def rowValueRealizer : Realizer rowValue :=
  composition (pair
    (composition (composition (pair (composition first second) second) (getDFast [])) listSum)
    (composition (pair (composition (composition first first) first) second) (getDFast 0))) subtract

lemma polynomial_rowValue : PolynomialTime rowValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast [])) polynomial_listSum)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first) polynomial_second) (polynomial_getDFast 0))) polynomial_subtract

def columnValues (z : EntryInput) : List ℕ := z.1.2.map (fun row=>row.getD z.2 0)

def columnValuesRealizer : Realizer columnValues :=
  composition (pair second (composition first second))
    (mapWith (composition (pair second first) (getDFast 0)))

lemma polynomial_columnValues : PolynomialTime columnValuesRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_second))
    (polynomial_mapWith (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_getDFast 0)))

def columnValue (z : EntryInput) : ℕ :=
  (columnValues z).sum-z.1.1.2.getD z.2 0

def columnValueRealizer : Realizer columnValue :=
  composition (pair (composition columnValuesRealizer listSum)
    (composition (pair (composition (composition first first) second) second) (getDFast 0))) subtract

lemma polynomial_columnValue : PolynomialTime columnValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_columnValues polynomial_listSum)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_second) (polynomial_getDFast 0))) polynomial_subtract

def rowIndices (z : Input) : List ℕ := List.range z.1.1.length
def columnIndices (z : Input) : List ℕ := List.range z.1.2.length

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

def complement (z : Input) : Input :=
  (((rowIndices z).map (fun i=>rowValue (z,i)),
    (columnIndices z).map (fun j=>columnValue (z,j))),z.2)

def complementRealizer : Realizer complement :=
  pair (pair
    (composition (pair identity rowIndicesRealizer) (mapWith rowValueRealizer))
    (composition (pair identity columnIndicesRealizer) (mapWith columnValueRealizer))) second

lemma polynomial_complement : PolynomialTime complementRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_rowIndices)
      (polynomial_mapWith polynomial_rowValue))
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_columnIndices)
      (polynomial_mapWith polynomial_columnValue))) polynomial_second

lemma rowValue_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (i : Fin m) :
    rowValue (data r c b,i.val)=BoundedTableComplement.rows b r i := by
  simp only [rowValue,data,ResidualGraphProgram.natCode,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta,List.sum_ofFn,
    BoundedTableComplement.rows,BoundedTableComplement.rowTotal]

lemma columnValue_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (j : Fin n) :
    columnValue (data r c b,j.val)=BoundedTableComplement.columns b c j := by
  simp only [columnValue,columnValues,data,ResidualGraphProgram.natCode,List.map_ofFn,
    Function.comp_def,List.getD_eq_getElem?_getD,List.getElem?_ofFn,j.isLt,
    dite_true,Option.getD_some,Fin.eta,List.sum_ofFn,
    BoundedTableComplement.columns,BoundedTableComplement.columnTotal]

lemma complement_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    complement (data r c b)=data (BoundedTableComplement.rows b r)
      (BoundedTableComplement.columns b c) b := by
  unfold complement
  apply Prod.ext
  · apply Prod.ext
    · simp only [rowIndices,data,List.length_ofFn,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,
        List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      exact rowValue_code r c b i
    · simp only [columnIndices,data,List.length_ofFn,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,
        List.map_ofFn]
      apply congrArg List.ofFn
      funext j
      exact columnValue_code r c b j
  · rfl

end ContingencyTables.BoundedComplementProgram

end OAI
