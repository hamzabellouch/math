import OAI.Combinatorics.ContingencyTables.Dense.DenseOffsetWidths
import OAI.Combinatorics.ContingencyTables.Machines.TranslationDecisionProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseSuccessCounts

namespace OAI

/-! # Reading the unique bin and offset of an accepted table -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary ProfilePrograms
open scoped BigOperators Classical

def tableFreeValue (z : ExponentData×(ℕ×ℕ)) : ℕ :=
  matrixEntry (z.1.1.2,(z.2.1+1,z.2.2+1))

def tableFreeValueRealizer : Realizer tableFreeValue :=
  composition (pair (composition (composition first first) second)
    (composition shiftedCellRealizer second)) matrixEntryRealizer

lemma polynomial_tableFreeValue : PolynomialTime tableFreeValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition polynomial_shiftedCell polynomial_second)) polynomial_matrixEntry

def tableBinCoordinate (z : ExponentData×(ℕ×ℕ)) : ℕ := tableFreeValue z/gridCellWidth z

def tableBinCoordinateRealizer : Realizer tableBinCoordinate :=
  composition (pair tableFreeValueRealizer gridCellWidthRealizer) quotient

lemma polynomial_tableBinCoordinate : PolynomialTime tableBinCoordinateRealizer :=
  polynomial_composition (polynomial_pair polynomial_tableFreeValue polynomial_gridCellWidth)
    polynomial_quotient

def tableOffsetCoordinate (z : ExponentData×(ℕ×ℕ)) : ℕ := tableFreeValue z%gridCellWidth z

def tableOffsetCoordinateRealizer : Realizer tableOffsetCoordinate :=
  composition (pair tableFreeValueRealizer gridCellWidthRealizer) remainder

lemma polynomial_tableOffsetCoordinate : PolynomialTime tableOffsetCoordinateRealizer :=
  polynomial_composition (polynomial_pair polynomial_tableFreeValue polynomial_gridCellWidth)
    polynomial_remainder

def tableFreeCells (z : ExponentData) : List (ℕ×ℕ) := freeCells (z,0)

def tableFreeCellsRealizer : Realizer tableFreeCells :=
  composition (pair identity (constant 0)) freeCellsRealizer

lemma polynomial_tableFreeCells : PolynomialTime tableFreeCellsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 0))
    polynomial_freeCells

def tableBinCoordinates (z : ExponentData) : List ℕ :=
  (tableFreeCells z).map (fun ij => tableBinCoordinate (z,ij))

def tableBinCoordinatesRealizer : Realizer tableBinCoordinates :=
  composition (pair identity tableFreeCellsRealizer) (mapWith tableBinCoordinateRealizer)

lemma polynomial_tableBinCoordinates : PolynomialTime tableBinCoordinatesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_tableFreeCells)
    (polynomial_mapWith polynomial_tableBinCoordinate)

def tableOffsetCoordinates (z : ExponentData) : List ℕ :=
  (tableFreeCells z).map (fun ij => tableOffsetCoordinate (z,ij))

def tableOffsetCoordinatesRealizer : Realizer tableOffsetCoordinates :=
  composition (pair identity tableFreeCellsRealizer) (mapWith tableOffsetCoordinateRealizer)

lemma polynomial_tableOffsetCoordinates : PolynomialTime tableOffsetCoordinatesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_tableFreeCells)
    (polynomial_mapWith polynomial_tableOffsetCoordinate)

def tableWidths (z : ExponentData) : List ℕ :=
  (tableFreeCells z).map (fun ij => gridCellWidth (z,ij))

def tableWidthsRealizer : Realizer tableWidths :=
  composition (pair identity tableFreeCellsRealizer) (mapWith gridCellWidthRealizer)

lemma polynomial_tableWidths : PolynomialTime tableWidthsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_tableFreeCells)
    (polynomial_mapWith polynomial_gridCellWidth)

def tableCoordinatesCode {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) : ExponentData :=
  (((marginCode R,marginCode P),tableOutput X),d)

lemma tableFreeValue_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) (i : Fin m) (j : Fin n) :
    tableFreeValue (tableCoordinatesCode R P d X,(i.val,j.val))=X.val (some i) (some j) := by
  exact tableOutput_entry R P X (some i) (some j)

lemma tableCellWidth_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) (i : Fin m) (j : Fin n) :
    gridCellWidth (tableCoordinatesCode R P d X,(i.val,j.val))=integerWidth R P d (i,j) := by
  have hr := marginCode_getD R (some i)
  have hc := marginCode_getD P (some j)
  change (marginCode R).getD (i.val+1) 0=R (some i) at hr
  change (marginCode P).getD (j.val+1) 0=P (some j) at hc
  simp only [gridCellWidth,shiftedCell,exponentCellData,tableCoordinatesCode,hr,hc]
  rfl

lemma tableBinCoordinate_code {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (X : Table R P) (i : Fin m) (j : Fin n) :
    tableBinCoordinate (tableCoordinatesCode R P d X,(i.val,j.val))=
      (corner (tableTrial R P d hd hR hP finProdFinEquiv X).1
        (finProdFinEquiv (i,j))).toNat := by
  rw [tableBinCoordinate,tableFreeValue_code,tableCellWidth_code]
  change _ = X.val (some ((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm
    (finProdFinEquiv (i,j))).1)
    (some (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2)/
      integerWidth R P d (finProdFinEquiv.symm (finProdFinEquiv (i,j)))
  rw [Equiv.symm_apply_apply]

lemma tableOffsetCoordinate_code {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (X : Table R P) (i : Fin m) (j : Fin n) :
    tableOffsetCoordinate (tableCoordinatesCode R P d X,(i.val,j.val))=
      ((tableTrial R P d hd hR hP finProdFinEquiv X).2 (i,j)).val := by
  rw [tableOffsetCoordinate,tableFreeValue_code,tableCellWidth_code]
  rfl

lemma tableFreeCells_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) :
    tableFreeCells (tableCoordinatesCode R P d X)=List.ofFn (fun v : Fin (m*n) =>
      (((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).1.val,
        (finProdFinEquiv.symm v).2.val)) := by
  simp only [tableFreeCells,freeCells,tableCoordinatesCode,marginCode,List.tail_cons]
  exact cellPairs_ofFn _ _

lemma tableBinCoordinates_code {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (X : Table R P) :
    tableBinCoordinates (tableCoordinatesCode R P d X)=
      gridNatCode (tableTrial R P d hd hR hP finProdFinEquiv X).1 := by
  rw [tableBinCoordinates,tableFreeCells_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  have he := tableBinCoordinate_code R P hd hR hP X
    ((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).1
    (finProdFinEquiv.symm v).2
  simpa only [Function.comp_apply,Prod.mk.eta,Equiv.apply_symm_apply] using he

lemma tableOffsetCoordinates_code {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (X : Table R P) :
    tableOffsetCoordinates (tableCoordinatesCode R P d X)=List.ofFn (fun v : Fin (m*n) =>
      ((tableTrial R P d hd hR hP finProdFinEquiv X).2 (finProdFinEquiv.symm v)).val) := by
  rw [tableOffsetCoordinates,tableFreeCells_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  exact tableOffsetCoordinate_code R P hd hR hP X
    ((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).1
    (finProdFinEquiv.symm v).2

lemma tableWidths_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) :
    tableWidths (tableCoordinatesCode R P d X)=List.ofFn (fun v : Fin (m*n) =>
      integerWidth R P d (finProdFinEquiv.symm v)) := by
  rw [tableWidths,tableFreeCells_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  exact tableCellWidth_code R P d X
    ((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).1
    (finProdFinEquiv.symm v).2

lemma tableOffsetLengths_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d h : ℕ) (X : Table R P) :
    offsetLengths (tableCoordinatesCode R P d X,h)=List.ofFn (fun v : Fin (m*n) =>
      FairBits.offsetBitLength (integerWidth R P d (finProdFinEquiv.symm v)) h d) := by
  change (tableFreeCells (tableCoordinatesCode R P d X)).map _=_
  rw [tableFreeCells_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  unfold offsetLength
  dsimp only [Function.comp_apply]
  rw [tableCellWidth_code]
  rfl

end ContingencyTables.DensePrograms

end OAI
