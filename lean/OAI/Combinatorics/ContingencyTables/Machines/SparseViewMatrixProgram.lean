import OAI.Combinatorics.ContingencyTables.Sampling.SmallViewLookupProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseIntegerProgram
import OAI.Combinatorics.ContingencyTables.Transport.DirectedBFSCode
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialGrid

namespace OAI

/-! # Materializing a sparse retained-cell view in a rectangular matrix -/

namespace ContingencyTables.SparseViewMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial ProfilePrograms DensePrograms

abbrev Input := (List ℕ × List ℕ) × (List (ℕ × ℕ) × List ℕ)
abbrev RowInput := Input × ℕ

def entry (z : RowInput × ℕ) : ℕ := lookupView (z.1.1.2,(z.1.2,z.2))
def entryRealizer : Realizer entry :=
  composition (f := fun z : RowInput × ℕ => (z.1.1.2,(z.1.2,z.2))) (g := lookupView)
    (pair (composition (composition first first) second)
      (pair (composition first second) second)) lookupViewRealizer
lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_lookupView

def columns (z : RowInput) : List ℕ := List.range z.1.1.2.length
def columnsRealizer : Realizer columns :=
  composition (composition (composition (composition first first) second) listLength) range
lemma polynomial_columns : PolynomialTime columnsRealizer := by
  apply polynomial_boundedRange (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.1.1.2).trans
    ((weight_snd z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))

def row (z : RowInput) : List ℕ := (columns z).map (fun j => entry (z,j))
def rowRealizer : Realizer row :=
  composition (pair identity columnsRealizer) (mapWith entryRealizer)
lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_columns)
    (polynomial_mapWith polynomial_entry)

def rowIndices (z : Input) : List ℕ := List.range z.1.1.length
def rowIndicesRealizer : Realizer rowIndices :=
  composition (composition (composition first first) listLength) range
lemma polynomial_rowIndices : PolynomialTime rowIndicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z))

def matrix (z : Input) : MatrixCode := (rowIndices z).map (fun i => row (z,i))
def matrixRealizer : Realizer matrix :=
  composition (pair identity rowIndicesRealizer) (mapWith rowRealizer)
theorem polynomial_matrix : PolynomialTime matrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_rowIndices)
    (polynomial_mapWith polynomial_row)

theorem matrix_ofFn {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (catalog : List (ℕ × ℕ)) (values : List ℕ) :
    matrix ((List.ofFn r,List.ofFn c),(catalog,values))=
      matrixCode (fun i : Fin m => fun j : Fin n =>
        lookupView ((catalog,values),(i.val,j.val))) := by
  simp only [matrix,rowIndices,row,columns,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn,Function.comp_def,entry,matrixCode]

end ContingencyTables.SparseViewMatrixProgram

end OAI
