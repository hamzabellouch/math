import OAI.Combinatorics.ContingencyTables.Dense.DenseScaleMatrixProgram
import OAI.Combinatorics.ContingencyTables.Machines.ScaledWordProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanOffsets

namespace OAI

/-! # Binary quotient offsets and the resulting free matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary

abbrev OffsetData := ExponentData×List (List Bool)

def offsetBits (z : OffsetData×(ℕ×ℕ)) : List Bool :=
  z.1.2.getD (z.2.1*z.1.1.1.1.2.tail.length+z.2.2) []

def offsetBitsRealizer : Realizer offsetBits := by
  let N : Realizer (fun z : OffsetData×(ℕ×ℕ) => z.1.1.1.1.2.tail) :=
    composition (composition (composition (composition
    (composition first first) first) first) second) tail
  let width := composition N listLength
  let index := composition (pair
    (composition (pair (composition second first) width) multiply)
    (composition second second)) add
  exact composition (pair (composition first second) index) (getDFast [])

theorem polynomial_offsetBits : PolynomialTime offsetBitsRealizer := by
  unfold offsetBitsRealizer
  apply polynomial_composition _ (polynomial_getDFast [])
  apply polynomial_pair (polynomial_composition polynomial_first polynomial_second)
  apply polynomial_composition _ polynomial_add
  apply polynomial_pair _ (polynomial_composition polynomial_second polynomial_second)
  apply polynomial_composition _ polynomial_multiply
  apply polynomial_pair (polynomial_composition polynomial_second polynomial_first)
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_first) polynomial_first) polynomial_second)
      polynomial_tail) polynomial_listLength

def offsetFreeEntry (z : OffsetData×(ℕ×ℕ)) : ℕ :=
  gridCellValue (z.1.1,z.2)+scaledWordValue (gridCellWidth (z.1.1,z.2),offsetBits z)

def offsetFreeEntryRealizer : Realizer offsetFreeEntry := by
  let cell : Realizer (fun z : OffsetData×(ℕ×ℕ) => (z.1.1,z.2)) :=
    pair (composition first first) second
  exact composition (pair (composition cell gridCellValueRealizer)
    (composition (pair (composition cell gridCellWidthRealizer) offsetBitsRealizer)
      scaledWordRealizer)) add

theorem polynomial_offsetFreeEntry : PolynomialTime offsetFreeEntryRealizer := by
  have hc : PolynomialTime (pair
      (composition (first (A := OffsetData) (B := ℕ×ℕ)) first) second) :=
    polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second
  unfold offsetFreeEntryRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition hc polynomial_gridCellValue)
    (polynomial_composition (polynomial_pair
      (polynomial_composition hc polynomial_gridCellWidth) polynomial_offsetBits)
      polynomial_scaledWord)) polynomial_add

def offsetRowEntry (z : (OffsetData×ℕ)×ℕ) : ℕ :=
  offsetFreeEntry (z.1.1,(z.1.2,z.2))

def offsetRowEntryRealizer : Realizer offsetRowEntry :=
  composition (pair (composition first first) (pair (composition first second) second))
    offsetFreeEntryRealizer

theorem polynomial_offsetRowEntry : PolynomialTime offsetRowEntryRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_offsetFreeEntry

def offsetRow (z : OffsetData×ℕ) : List ℕ :=
  (scaleColumns z.1.1).map (fun j => offsetRowEntry (z,j))

def offsetRowRealizer : Realizer offsetRow :=
  composition (pair identity (composition (composition first first) scaleColumnsRealizer))
    (mapWith offsetRowEntryRealizer)

theorem polynomial_offsetRow : PolynomialTime offsetRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_scaleColumns))
    (polynomial_mapWith polynomial_offsetRowEntry)

def offsetMatrix (z : OffsetData) : MatrixCode :=
  (scaleRows z.1).map (fun i => offsetRow (z,i))

def offsetMatrixRealizer : Realizer offsetMatrix :=
  composition (pair identity (composition first scaleRowsRealizer)) (mapWith offsetRowRealizer)

theorem polynomial_offsetMatrix : PolynomialTime offsetMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_scaleRows)) (polynomial_mapWith polynomial_offsetRow)

end ContingencyTables.DensePrograms

end OAI
