import OAI.Combinatorics.ContingencyTables.Dense.DenseMatrixTable
import OAI.Combinatorics.ContingencyTables.Machines.IntegerMatrixProgram

namespace OAI

/-! # Polynomial assembly of the dense count matrix in column order -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

abbrev CountMatrixContext := (List Bool×ℕ)×((List ℕ×List ℕ)×ℕ)
abbrev CountMatrixData := CountMatrixContext×List (List ℕ)

def countMatrixEntryInput (z : (CountMatrixData×List ℕ)×List ℕ) : CountRowData×List ℕ :=
  ((((z.1.1.1.1,((z.1.1.1.2.1,z.2),z.1.1.1.2.2)),z.1.1.2)),z.1.2)

def countMatrixEntryInputRealizer : Realizer countMatrixEntryInput := by
  let data : Realizer (fun z : (CountMatrixData×List ℕ)×List ℕ => z.1.1) :=
    composition first first
  let ctx := composition data first
  let margins := composition (composition ctx second) first
  let d := composition (composition ctx second) second
  let rowData := pair (pair (composition ctx first) (pair (pair margins second) d))
    (composition data second)
  exact pair rowData (composition first second)

lemma polynomial_countMatrixEntryInput : PolynomialTime countMatrixEntryInputRealizer := by
  have hd : PolynomialTime (composition
      (first (A := CountMatrixData×List ℕ) (B := List ℕ)) first) :=
    polynomial_composition polynomial_first polynomial_first
  have hc := polynomial_composition hd polynomial_first
  have hm := polynomial_composition (polynomial_composition hc polynomial_second) polynomial_first
  have hp := polynomial_composition (polynomial_composition hc polynomial_second) polynomial_second
  unfold countMatrixEntryInputRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition hc polynomial_first)
    (polynomial_pair (polynomial_pair hm polynomial_second) hp))
    (polynomial_composition hd polynomial_second))
    (polynomial_composition polynomial_first polynomial_second)

def countMatrixEntry (z : (CountMatrixData×List ℕ)×List ℕ) : ℕ :=
  rowEntry (countMatrixEntryInput z)

def countMatrixEntryRealizer : Realizer countMatrixEntry :=
  composition countMatrixEntryInputRealizer rowEntryRealizer

lemma polynomial_countMatrixEntry : PolynomialTime countMatrixEntryRealizer :=
  polynomial_composition polynomial_countMatrixEntryInput polynomial_rowEntry

def countColumn (z : CountMatrixData×List ℕ) : List ℕ :=
  z.1.2.map (fun a => countMatrixEntry (z,a))

def countColumnRealizer : Realizer countColumn :=
  composition (pair identity (composition first second)) (mapWith countMatrixEntryRealizer)

lemma polynomial_countColumn : PolynomialTime countColumnRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_second))
    (polynomial_mapWith polynomial_countMatrixEntry)

def countMatrix (z : CountMatrixData) : List (List ℕ) :=
  z.2.map (fun b => countColumn (z,b))

def countMatrixRealizer : Realizer countMatrix :=
  composition (pair identity second) (mapWith countColumnRealizer)

/-- Preparation explicitly contains all states and one unary acceptance
allowance. Matrix construction is polynomial in precisely that data. -/
theorem polynomial_countMatrix : PolynomialTime countMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_second)
    (polynomial_mapWith polynomial_countColumn)

lemma countMatrix_actual {m n d N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d)
    (e : Fin N ≃ Grid (I := Fin (m*n)) (4*d^8))
    (xs : List Bool) (hxs : xs.length=8*d^5) :
    countMatrix ((((xs,2^denseStepBits d),((marginCode R,marginCode P),d)),
      List.ofFn (fun i => gridNatCode (e i))))=
        List.ofFn (fun j => List.ofFn (fun i =>
          denseTransitionCount R P d finProdFinEquiv (e i) (e j))) := by
  simp only [countMatrix,countColumn,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  apply congrArg List.ofFn
  funext i
  exact rowEntry_actual R P hq e xs hxs (e i) (e j)

end ContingencyTables.DensePrograms

end OAI
