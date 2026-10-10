import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTransitionProgram

namespace OAI

/-! # Reconstructing and testing an original table from an outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms Polynomial

abbrev OuterTableData :=
  ((List (ℕ×ℕ)×(List ℕ×List ℕ))×(List ℕ×List ℕ))×((ℕ×ℕ)×MatrixCode)
abbrev OuterTableCell := OuterTableData×(ℕ×ℕ)

def outputCellPosition (z : OuterTableCell) : ℕ := z.1.1.1.1.idxOf z.2
def outputCellPositionRealizer : Realizer outputCellPosition :=
  composition (pair second (composition (composition (composition first first) first) first))
    cellLookupRealizer

theorem polynomial_outputCellPosition : PolynomialTime outputCellPositionRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first))
    polynomial_cellLookup

def outputSmallEntry (z : OuterTableCell) : ℕ := z.1.1.1.2.1.getD (outputCellPosition z) 0
def outputSmallEntryRealizer : Realizer outputSmallEntry :=
  composition (pair (composition (composition (composition (composition first first) first) second) first)
    outputCellPositionRealizer) (getDFast 0)

theorem polynomial_outputSmallEntry : PolynomialTime outputSmallEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_first) polynomial_outputCellPosition) (polynomial_getDFast 0)

def outputDensePosition (z : OuterTableCell) : ℕ×ℕ :=
  (z.1.1.2.1.idxOf z.2.1,z.1.1.2.2.idxOf z.2.2)
def outputDensePositionRealizer : Realizer outputDensePosition :=
  pair (composition (pair (composition second first)
    (composition (composition (composition first first) second) first)) (indexOf natEqual))
    (composition (pair (composition second second)
      (composition (composition (composition first first) second) second)) (indexOf natEqual))

theorem polynomial_outputDensePosition : PolynomialTime outputDensePositionRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first))
      (polynomial_indexOf polynomial_natEqual))
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second))
      (polynomial_indexOf polynomial_natEqual))

def outputLargeEntry (z : OuterTableCell) : ℕ :=
  matrixEntry (z.1.2.2,outputDensePosition z)-z.1.2.1.2
def outputLargeEntryRealizer : Realizer outputLargeEntry :=
  composition (pair (composition (pair (composition (composition first second) second)
      outputDensePositionRealizer) matrixEntryRealizer)
    (composition (composition (composition first second) first) second)) subtract

theorem polynomial_outputLargeEntry : PolynomialTime outputLargeEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_outputDensePosition) polynomial_matrixEntry)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first) polynomial_second))
    polynomial_subtract

def outputEntry (z : OuterTableCell) : ℕ :=
  if outputCellPosition z < z.1.1.1.1.length then outputSmallEntry z else outputLargeEntry z
def outputEntryRealizer : Realizer outputEntry :=
  (choose (composition (pair outputCellPositionRealizer
      (composition (composition (composition (composition first first) first) first) listLength)) less)
    outputSmallEntryRealizer outputLargeEntryRealizer).congr
      (by intro z; simp only [Function.comp_apply,decide_eq_true_eq,outputEntry])

theorem polynomial_outputEntry : PolynomialTime outputEntryRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_outputCellPosition
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
        polynomial_listLength)) polynomial_less)
    polynomial_outputSmallEntry polynomial_outputLargeEntry)

def paddingTest (z : ℕ×MatrixCode) : Bool := z.2.all (fun row => row.all (fun a => decide (z.1≤a)))
def paddingTestRealizer : Realizer paddingTest :=
  (composition (mapWith (composition (mapWith leNat) all)) all).congr
    (by intro z; simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,paddingTest])

theorem polynomial_paddingTest : PolynomialTime paddingTestRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_mapWith (polynomial_composition (polynomial_mapWith polynomial_leNat) polynomial_all))
    polynomial_all)

def outerSuccess (z : OuterTableData) : Bool :=
  balancedTest (z.1.1.2,z.2.1.1) && paddingTest (z.2.1.2,z.2.2)

def outerSuccessRealizer : Realizer outerSuccess :=
  composition (pair
    (composition (pair (composition (composition first first) second)
      (composition (composition second first) first)) balancedTestRealizer)
    (composition (pair (composition (composition second first) second)
      (composition second second)) paddingTestRealizer)) boolAnd

theorem polynomial_outerSuccess : PolynomialTime outerSuccessRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_first))
      polynomial_balancedTest)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_paddingTest)) polynomial_boolAnd

abbrev OuterMatrixInput := (List ℕ×List ℕ)×OuterTableData

def outputShape (z : OuterMatrixInput) : CompletionData := (z.1,[])
def outputShapeRealizer : Realizer outputShape := pair first (constant [])

theorem polynomial_outputShape : PolynomialTime outputShapeRealizer :=
  polynomial_pair polynomial_first (polynomial_constant [])

def outputRows (z : OuterMatrixInput) : List ℕ := completionRows (outputShape z)
def outputColumns (z : OuterMatrixInput) : List ℕ := completionColumns (outputShape z)
def outputRowsRealizer : Realizer outputRows := composition outputShapeRealizer completionRowsRealizer
def outputColumnsRealizer : Realizer outputColumns := composition outputShapeRealizer completionColumnsRealizer

theorem polynomial_outputRows : PolynomialTime outputRowsRealizer :=
  polynomial_composition polynomial_outputShape polynomial_completionRows
theorem polynomial_outputColumns : PolynomialTime outputColumnsRealizer :=
  polynomial_composition polynomial_outputShape polynomial_completionColumns

def outputRowEntry (z : (OuterMatrixInput×ℕ)×ℕ) : ℕ := outputEntry (z.1.1.2,(z.1.2,z.2))
def outputRowEntryRealizer : Realizer outputRowEntry :=
  composition (pair (composition (composition first first) second)
    (pair (composition first second) second)) outputEntryRealizer

theorem polynomial_outputRowEntry : PolynomialTime outputRowEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_outputEntry

def outputRow (z : OuterMatrixInput×ℕ) : List ℕ :=
  (outputColumns z.1).map (fun j => outputRowEntry (z,j))
def outputRowRealizer : Realizer outputRow :=
  composition (pair identity (composition first outputColumnsRealizer)) (mapWith outputRowEntryRealizer)

theorem polynomial_outputRow : PolynomialTime outputRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_outputColumns))
    (polynomial_mapWith polynomial_outputRowEntry)

def outputMatrix (z : OuterMatrixInput) : MatrixCode :=
  (outputRows z).map (fun i => outputRow (z,i))
def outputMatrixRealizer : Realizer outputMatrix :=
  composition (pair identity outputRowsRealizer) (mapWith outputRowRealizer)

theorem polynomial_outputMatrix : PolynomialTime outputMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_outputRows)
    (polynomial_mapWith polynomial_outputRow)

def acceptedTable (z : OuterMatrixInput) : Option MatrixCode :=
  if outerSuccess z.2 then some (outputMatrix z) else none
def acceptedTableRealizer : Realizer acceptedTable :=
  choose (composition second outerSuccessRealizer)
    (composition outputMatrixRealizer MatchingFPRAS.TreeTyped.some) (constant none)

theorem polynomial_acceptedTable : PolynomialTime acceptedTableRealizer :=
  polynomial_choose (polynomial_composition polynomial_second polynomial_outerSuccess)
    (polynomial_composition polynomial_outputMatrix polynomial_some) (polynomial_constant none)

end ContingencyTables.ProfilePrograms

end OAI
