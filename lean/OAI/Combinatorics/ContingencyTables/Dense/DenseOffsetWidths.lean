import OAI.Combinatorics.ContingencyTables.Dense.DenseOffsetTrial
import OAI.Combinatorics.ContingencyTables.Dense.DenseWordProgram
import OAI.Combinatorics.ContingencyTables.Machines.DependentWordProgram

namespace OAI

/-! # Computing the actual variable-width offset word layout -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary FairBits

abbrev OffsetWidthData := ExponentData×ℕ

def offsetLength (z : OffsetWidthData×(ℕ×ℕ)) : ℕ :=
  Nat.clog 2 (gridCellWidth (z.1.1,z.2)+1)+4*(z.1.2+z.1.1.2)

def offsetLengthRealizer : Realizer offsetLength := by
  let cell : Realizer (fun z : OffsetWidthData×(ℕ×ℕ) => (z.1.1,z.2)) :=
    pair (composition first first) second
  let width := composition (composition (composition cell gridCellWidthRealizer) successor)
    ceilLogTwoRealizer
  let H : Realizer (fun z : OffsetWidthData×(ℕ×ℕ) => z.1.2) := composition first second
  let D : Realizer (fun z : OffsetWidthData×(ℕ×ℕ) => z.1.1.2) :=
    composition (composition first first) second
  let hd := composition (pair H D) add
  let accuracy := composition (pair (constant 4) hd) multiply
  exact composition (pair width accuracy) add

theorem polynomial_offsetLength : PolynomialTime offsetLengthRealizer := by
  have hc : PolynomialTime (pair
      (composition (first (A := OffsetWidthData) (B := ℕ×ℕ)) first) second) :=
    polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second
  unfold offsetLengthRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition hc polynomial_gridCellWidth) polynomial_successor) polynomial_ceilLogTwo)
    (polynomial_composition (polynomial_pair (polynomial_constant 4)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_second)
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
        polynomial_add)) polynomial_multiply)) polynomial_add

def freeCells (z : OffsetWidthData) : List (ℕ×ℕ) :=
  cellPairs (z.1.1.1.1.tail,z.1.1.1.2.tail)

def freeCellsRealizer : Realizer freeCells :=
  composition (pair
    (composition (composition (composition (composition first first) first) first) tail)
    (composition (composition (composition (composition first first) first) second) tail)) cellPairsRealizer

theorem polynomial_freeCells : PolynomialTime freeCellsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first) polynomial_tail)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second) polynomial_tail))
    polynomial_cellPairs

def offsetLengths (z : OffsetWidthData) : List ℕ :=
  (freeCells z).map (fun ij => offsetLength (z,ij))

def offsetLengthsRealizer : Realizer offsetLengths :=
  composition (pair identity freeCellsRealizer) (mapWith offsetLengthRealizer)

theorem polynomial_offsetLengths : PolynomialTime offsetLengthsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_freeCells)
    (polynomial_mapWith polynomial_offsetLength)

lemma cellPairs_ofFn {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    cellPairs (List.ofFn r,List.ofFn c)=List.ofFn (fun v : Fin (m*n) =>
      (((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).1.val,
        ((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).2.val)) := by
  apply List.ext_getElem
  · simp only [cellPairs,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    simp only [cellPairs,List.getElem_map,List.getElem_range,List.getElem_ofFn,pairAt,List.length_ofFn]
    rfl

noncomputable section
open scoped Classical

lemma offsetLength_code {m n q K : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d h : ℕ) (a : Grid (I := Fin q) K) (e : Fin m×Fin n ≃ Fin q) (i : Fin m) (j : Fin n) :
    offsetLength ((exponentDataCode R P d
      (fun i j => (corner a (e (i,j))).toNat),h),(i.val,j.val))=
      offsetBitLength (integerWidth R P d (i,j)) h d := by
  change Nat.clog 2 (gridCellWidth (exponentDataCode R P d
    (fun i j => (corner a (e (i,j))).toNat),(i.val,j.val))+1)+4*(h+d)=_
  rw [gridCellWidth_code]
  rfl

theorem offsetLengths_code {m n K : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d h : ℕ) (a : Grid (I := Fin (m*n)) K) :
    offsetLengths (exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat),h)=
      List.ofFn (fun v : Fin (m*n) => offsetBitLength
        (integerWidth R P d (finProdFinEquiv.symm v)) h d) := by
  unfold offsetLengths freeCells
  simp only [exponentDataCode,marginCode,List.tail_cons]
  rw [cellPairs_ofFn,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  exact offsetLength_code R P d h a finProdFinEquiv
    (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2

end
end ContingencyTables.DensePrograms

end OAI
