import OAI.Combinatorics.ContingencyTables.Dense.DenseExponentListSemantics

namespace OAI

/-! # Binary conversion from a grid coordinate to a free integer entry -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open GridBoundary

def shiftedCell (z : ExponentData×(ℕ×ℕ)) : ExponentData×(ℕ×ℕ) :=
  (z.1,(z.2.1+1,z.2.2+1))

def shiftedCellRealizer : Realizer shiftedCell :=
  pair first (pair (composition (composition second first) successor)
    (composition (composition second second) successor))

lemma polynomial_shiftedCell : PolynomialTime shiftedCellRealizer :=
  polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_successor)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_successor))

def gridCellWidth (z : ExponentData×(ℕ×ℕ)) : ℕ :=
  (exponentCellData (shiftedCell z)).1.2/z.1.2^8

def gridCellWidthRealizer : Realizer gridCellWidth :=
  composition (pair
    (composition (composition (composition shiftedCellRealizer exponentCellDataRealizer) first) second)
    (composition (composition first second) eighthPower)) quotient

theorem polynomial_gridCellWidth : PolynomialTime gridCellWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_shiftedCell polynomial_exponentCellData) polynomial_first)
      polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_eighthPower)) polynomial_quotient

def gridCellValue (z : ExponentData×(ℕ×ℕ)) : ℕ :=
  gridCellWidth z*matrixEntry (z.1.1.2,z.2)

def gridCellValueRealizer : Realizer gridCellValue :=
  composition (pair gridCellWidthRealizer
    (composition (pair (composition (composition first first) second) second) matrixEntryRealizer))
    multiply

theorem polynomial_gridCellValue : PolynomialTime gridCellValueRealizer :=
  polynomial_composition (polynomial_pair polynomial_gridCellWidth
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_second) polynomial_matrixEntry)) polynomial_multiply

variable {m n q K : ℕ}

theorem gridCellValue_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin q) K) (e : Fin m×Fin n ≃ Fin q)
    (i : Fin m) (j : Fin n) :
    gridCellValue (exponentDataCode R P d
      (fun i j => (corner a (e (i,j))).toNat),(i.val,j.val))=
      cornerFree R P d e a (i,j) := by
  have hR := marginCode_getD R (some i)
  have hP := marginCode_getD P (some j)
  change (marginCode R).getD (i.val+1) 0=R (some i) at hR
  change (marginCode P).getD (j.val+1) 0=P (some j) at hP
  simp only [gridCellValue,gridCellWidth,shiftedCell,exponentCellData,exponentDataCode,
    hR,hP,matrixEntry_code,cornerFree,integerWidth]

end ContingencyTables.DensePrograms

end OAI
