import OAI.Combinatorics.ContingencyTables.Dense.DenseIntegerProgram
import OAI.Combinatorics.ContingencyTables.Transport.DirectedBFSCode
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialGrid

namespace OAI

/-! # Entrywise natural subtraction on a supplied matrix shape -/

namespace ContingencyTables.MatrixSubtractProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms

abbrev Input := MatrixCode × MatrixCode
abbrev RowInput := Input × ℕ

def entry (z : RowInput × ℕ) : ℕ :=
  matrixEntry (z.1.1.1,(z.1.2,z.2))-matrixEntry (z.1.1.2,(z.1.2,z.2))
def entryRealizer : Realizer entry := by
  let left : Realizer (fun z : RowInput × ℕ => matrixEntry (z.1.1.1,(z.1.2,z.2))) :=
    composition (f := fun z : RowInput × ℕ => (z.1.1.1,(z.1.2,z.2))) (g := matrixEntry)
      (pair (composition (composition first first) first)
        (pair (composition first second) second)) matrixEntryRealizer
  let right : Realizer (fun z : RowInput × ℕ => matrixEntry (z.1.1.2,(z.1.2,z.2))) :=
    composition (f := fun z : RowInput × ℕ => (z.1.1.2,(z.1.2,z.2))) (g := matrixEntry)
      (pair (composition (composition first first) second)
        (pair (composition first second) second)) matrixEntryRealizer
  exact composition (f := fun z : RowInput × ℕ =>
    (matrixEntry (z.1.1.1,(z.1.2,z.2)),matrixEntry (z.1.1.2,(z.1.2,z.2))))
    (g := fun p : ℕ × ℕ => p.1-p.2) (pair left right) subtract
lemma polynomial_entry : PolynomialTime entryRealizer := by
  unfold entryRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_matrixEntry)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_matrixEntry)) polynomial_subtract

def sourceRow (z : RowInput) : List ℕ := z.1.1.getD z.2 []
def sourceRowRealizer : Realizer sourceRow :=
  composition (pair (composition first first) second) (getDFast [])
lemma polynomial_sourceRow : PolynomialTime sourceRowRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_getDFast [])

def columns (z : RowInput) : List ℕ := List.range (sourceRow z).length
def columnsRealizer : Realizer columns :=
  composition (f := sourceRow) (g := fun xs : List ℕ => List.range xs.length)
    sourceRowRealizer (composition listLength range)
lemma polynomial_columns : PolynomialTime columnsRealizer := by
  apply polynomial_composition polynomial_sourceRow
  apply polynomial_boundedRange polynomial_listLength X
  intro xs
  simpa only [eval_X] using list_length_le_weight xs

def row (z : RowInput) : List ℕ := (columns z).map (fun j => entry (z,j))
def rowRealizer : Realizer row :=
  composition (pair identity columnsRealizer) (mapWith entryRealizer)
lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_columns)
    (polynomial_mapWith polynomial_entry)

def indices (z : Input) : List ℕ := List.range z.1.length
def indicesRealizer : Realizer indices := composition (composition first listLength) range
lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

def matrix (z : Input) : MatrixCode := (indices z).map (fun i => row (z,i))
def matrixRealizer : Realizer matrix :=
  composition (pair identity indicesRealizer) (mapWith rowRealizer)
theorem polynomial_matrix : PolynomialTime matrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_row)

theorem matrix_code {m n : ℕ} (B Y : Fin m → Fin n → ℕ) :
    matrix (matrixCode B,matrixCode Y)=matrixCode (fun i j => B i j-Y i j) := by
  simp only [matrix,indices,matrixCode,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  simp only [row,columns,sourceRow,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,dite_true,Option.getD_some,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn,Function.comp_def,entry]
  apply congrArg List.ofFn
  funext j
  exact congrArg₂ Nat.sub (matrixEntry_code B i j) (matrixEntry_code Y i j)

end ContingencyTables.MatrixSubtractProgram

end OAI
