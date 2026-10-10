import OAI.Combinatorics.ContingencyTables.Machines.PreparedOffsetCount
import OAI.Combinatorics.ContingencyTables.Dense.GridIndexProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseTableCoordinates
import OAI.Combinatorics.ContingencyTables.Dense.DenseWalkTabulation

namespace OAI

/-! # Computing one accepted-table numerator from the cached bin vector -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

/-- Cached walk vector, shared bit allowance, and the table/margin data
with the requested precision. -/
abbrev TrialCountData := (List ℕ×List Bool)×OffsetWidthData

def trialCountIndexInput (z : TrialCountData) : GridIndexData :=
  (tableBinCoordinates z.2.1,4*z.2.1.2^8)

def trialCountIndexInputRealizer : Realizer trialCountIndexInput := by
  let data : Realizer (fun z : TrialCountData => z.2.1) := composition second first
  let d := composition data second
  let K := composition (pair (constant 4) (composition d eighthPower)) multiply
  exact pair (composition data tableBinCoordinatesRealizer) K

lemma polynomial_trialCountIndexInput : PolynomialTime trialCountIndexInputRealizer := by
  have hd : PolynomialTime (composition
      (second (A := List ℕ×List Bool) (B := OffsetWidthData)) first) :=
    polynomial_composition polynomial_second polynomial_first
  have hK := polynomial_composition (polynomial_pair (polynomial_constant 4)
    (polynomial_composition (polynomial_composition hd polynomial_second)
      polynomial_eighthPower)) polynomial_multiply
  unfold trialCountIndexInputRealizer
  exact polynomial_pair (polynomial_composition hd polynomial_tableBinCoordinates) hK

def trialCountOffsetInput (z : TrialCountData) : PreparedOffsetData :=
  (((z.1.2,tableWidths z.2.1),offsetLengths z.2),tableOffsetCoordinates z.2.1)

def trialCountOffsetInputRealizer : Realizer trialCountOffsetInput := by
  let data : Realizer (fun z : TrialCountData => z.2.1) := composition second first
  exact pair (pair (pair (composition first second) (composition data tableWidthsRealizer))
    (composition second offsetLengthsRealizer)) (composition data tableOffsetCoordinatesRealizer)

lemma polynomial_trialCountOffsetInput : PolynomialTime trialCountOffsetInputRealizer := by
  have hd : PolynomialTime (composition
      (second (A := List ℕ×List Bool) (B := OffsetWidthData)) first) :=
    polynomial_composition polynomial_second polynomial_first
  unfold trialCountOffsetInputRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition hd polynomial_tableWidths))
    (polynomial_composition polynomial_second polynomial_offsetLengths))
    (polynomial_composition hd polynomial_tableOffsetCoordinates)

def trialTableCount (z : TrialCountData) : ℕ :=
  z.1.1.getD (gridIndex (trialCountIndexInput z)) 0*
    preparedOffsetProduct (trialCountOffsetInput z)

def trialTableCountRealizer : Realizer trialTableCount := by
  let idx := composition trialCountIndexInputRealizer gridIndexRealizer
  let bin := composition (pair (composition first first) idx) (getDFast 0)
  let offs := composition trialCountOffsetInputRealizer preparedOffsetProductRealizer
  let result := composition (pair bin offs) multiply
  exact result

/-- Once the bin vector is cached, one accepted-table numerator uses
polynomial binary arithmetic and one lookup. -/
theorem polynomial_trialTableCount : PolynomialTime trialTableCountRealizer := by
  unfold trialTableCountRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition polynomial_trialCountIndexInput polynomial_gridIndex))
      (polynomial_getDFast 0))
    (polynomial_composition polynomial_trialCountOffsetInput polynomial_preparedOffsetProduct))
    polynomial_multiply

/-- The program computes the count of the unique accepted trial for this
table, using canonical walk tabulation. -/
theorem trialTableCount_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (h : ℕ)
    (cap : List Bool)
    (hcap : ∀ j : Fin (m*n),
      FairBits.offsetBitLength (integerWidth R P d (finProdFinEquiv.symm j)) h d≤cap.length)
    (X : Table R P) :
    trialTableCount ((tabulateDenseWalk ((marginCode R,marginCode P),(d,h)),cap),
      (tableCoordinatesCode R P d X,h))=
    (denseTrialCounts R P d hd hR hP finProdFinEquiv h
      (canonicalOrigin (m*n) d (by omega))).count
        (tableTrial R P d hd hR hP finProdFinEquiv X) := by
  unfold trialTableCount trialCountIndexInput trialCountOffsetInput
  change (tabulateDenseWalk ((marginCode R,marginCode P),(d,h))).getD
      (gridIndex (tableBinCoordinates (tableCoordinatesCode R P d X),4*d^8)) 0*
    preparedOffsetProduct (((cap,tableWidths (tableCoordinatesCode R P d X)),
      offsetLengths (tableCoordinatesCode R P d X,h)),
      tableOffsetCoordinates (tableCoordinatesCode R P d X))=_
  rw [tableBinCoordinates_code R P hd hR hP X,gridIndex_code,
    tableWidths_code,tableOffsetLengths_code,tableOffsetCoordinates_code R P hd hR hP X,
    preparedOffsetProduct_ofFn cap _ _ _ hcap,
    tabulateDenseWalk_actual R P hq (by omega) h]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,Fin.isLt,
    dite_true,Option.getD_some,Fin.eta,Equiv.apply_symm_apply]
  exact denseTrial_table_count R P d hd hR hP finProdFinEquiv h
    (canonicalOrigin (m*n) d (by omega)) X |>.symm

end ContingencyTables.DensePrograms

end OAI
