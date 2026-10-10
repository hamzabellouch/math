import OAI.Combinatorics.ContingencyTables.Dense.DenseTableCoordinates
import OAI.Combinatorics.ContingencyTables.Dense.GridIndexProgram
import OAI.Combinatorics.ContingencyTables.Transport.IndexedTableLaw

namespace OAI

/-! # Computing the position of a table in the completion enumeration -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def tableFreeCoordinates (z : ExponentData) : List ℕ :=
  (tableFreeCells z).map (fun ij => tableFreeValue (z,ij))

def tableFreeCoordinatesRealizer : Realizer tableFreeCoordinates :=
  composition (pair identity tableFreeCellsRealizer) (mapWith tableFreeValueRealizer)

lemma polynomial_tableFreeCoordinates : PolynomialTime tableFreeCoordinatesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_tableFreeCells)
    (polynomial_mapWith polynomial_tableFreeValue)

lemma tableFreeCoordinates_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) :
    tableFreeCoordinates (tableCoordinatesCode R P d X)=
      List.ofFn (fun k : Fin (m*n) =>
        X.val (some (finProdFinEquiv.symm k).1) (some (finProdFinEquiv.symm k).2)) := by
  rw [tableFreeCoordinates,tableFreeCells_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  exact tableFreeValue_code R P d X _ _

def tableIndexInput (z : CompletionData) : GridIndexData :=
  (tableFreeCoordinates (z,0),z.1.1.sum+1)

def tableIndexInputRealizer : Realizer tableIndexInput :=
  pair (composition (pair identity (constant 0)) tableFreeCoordinatesRealizer)
    (composition (composition (composition first first) listSum) successor)

lemma polynomial_tableIndexInput : PolynomialTime tableIndexInputRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_constant 0)) polynomial_tableFreeCoordinates)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_listSum)
      polynomial_successor)

def tableIndex (z : CompletionData) : ℕ := gridIndex (tableIndexInput z)

def tableIndexRealizer : Realizer tableIndex :=
  composition tableIndexInputRealizer gridIndexRealizer

theorem polynomial_tableIndex : PolynomialTime tableIndexRealizer :=
  polynomial_composition polynomial_tableIndexInput polynomial_gridIndex

theorem tableIndex_actual {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (X : Table R P) :
    tableIndex ((marginCode R,marginCode P),tableOutput X)=
      (IndexedTableLaw.index R P (le_refl (∑ i,R i)) X).val := by
  unfold tableIndex tableIndexInput
  change gridIndex (tableFreeCoordinates (tableCoordinatesCode R P 0 X),
    (marginCode R).sum+1)=_
  rw [tableFreeCoordinates_code]
  have hsum : (marginCode R).sum=∑ i,R i := by
    simp only [marginCode,List.sum_cons,List.sum_ofFn,Fintype.sum_option]
  rw [hsum]
  change gridIndex (List.ofFn (fun k =>
    (BoxCompletion.encode R P (le_refl (∑ i,R i)) X k).val),(∑ i,R i)+1)=_
  rw [gridIndex_ofFn]
  rfl

end ContingencyTables.DensePrograms

end OAI
