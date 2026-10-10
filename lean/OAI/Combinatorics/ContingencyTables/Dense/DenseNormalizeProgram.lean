import OAI.Combinatorics.ContingencyTables.Dense.DenseSwapProgram

namespace OAI

/-! # Moving maximal margins into the distinguished positions -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def swapMargins (z : (ℕ×ℕ)×(List ℕ×List ℕ)) : List ℕ×List ℕ :=
  (swapZeroList (z.1.1,z.2.1),swapZeroList (z.1.2,z.2.2))

def swapMarginsRealizer : Realizer swapMargins :=
  pair (composition (pair (composition first first) (composition second first)) swapZeroListRealizer)
    (composition (pair (composition first second) (composition second second)) swapZeroListRealizer)

theorem polynomial_swapMargins : PolynomialTime swapMarginsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition polynomial_second polynomial_first)) polynomial_swapZeroList)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_swapZeroList)

def swapFlatData (z : (ℕ×ℕ)×FlatExponentData) : FlatExponentData :=
  ((swapMargins (z.1,z.2.1.1),z.2.1.2),z.2.2)

def swapFlatDataRealizer : Realizer swapFlatData := by
  let data : Realizer (fun z : (ℕ×ℕ)×FlatExponentData => z.2) := second
  let margins := composition (pair first (composition (composition data first) first)) swapMarginsRealizer
  exact pair (pair margins (composition (composition data first) second)) (composition data second)

theorem polynomial_swapFlatData : PolynomialTime swapFlatDataRealizer := by
  unfold swapFlatDataRealizer
  exact polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_first))
      polynomial_swapMargins)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second))
    (polynomial_composition polynomial_second polynomial_second)

def permuteDrawData (z : (ℕ×ℕ)×DenseDrawData) : DenseDrawData :=
  (((swapFlatData (z.1,z.2.1.1.1),z.2.1.1.2),swapMatrix (z.1,z.2.1.2)),z.2.2)

def permuteDrawDataRealizer : Realizer permuteDrawData := by
  let draw : Realizer (fun z : (ℕ×ℕ)×DenseDrawData => z.2) := second
  let params := composition (composition draw first) first
  let data := composition (pair first (composition params first)) swapFlatDataRealizer
  let fallback := composition (pair first (composition (composition draw first) second)) swapMatrixRealizer
  exact pair (pair (pair data (composition params second)) fallback) (composition draw second)

theorem polynomial_permuteDrawData : PolynomialTime permuteDrawDataRealizer := by
  unfold permuteDrawDataRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
        polynomial_first) polynomial_first)) polynomial_swapFlatData)
    (polynomial_composition (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_first) polynomial_second))
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second))
      polynomial_swapMatrix)) (polynomial_composition polynomial_second polynomial_second)

def marginIndices (z : List ℕ×List ℕ) : ℕ×ℕ := (maximumIndex z.1,maximumIndex z.2)
def marginIndicesRealizer : Realizer marginIndices :=
  pair (composition first maximumIndexRealizer) (composition second maximumIndexRealizer)

theorem polynomial_marginIndices : PolynomialTime marginIndicesRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_maximumIndex)
    (polynomial_composition polynomial_second polynomial_maximumIndex)

def drawIndices (z : DenseDrawData) : ℕ×ℕ := marginIndices z.1.1.1.1.1

def drawIndicesRealizer : Realizer drawIndices := by
  let margins : Realizer (fun z : DenseDrawData => z.1.1.1.1.1) :=
    composition (composition (composition (composition first first) first) first) first
  exact composition margins marginIndicesRealizer

theorem polynomial_drawIndices : PolynomialTime drawIndicesRealizer := by
  unfold drawIndicesRealizer
  exact polynomial_composition (polynomial_composition
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_first) polynomial_first) polynomial_first)
    polynomial_marginIndices

def preparedDraw (z : DenseDrawData) : DenseDrawData :=
  permuteDrawData (drawIndices z,z)

def preparedDrawRealizer : Realizer preparedDraw :=
  composition (pair drawIndicesRealizer identity) permuteDrawDataRealizer

theorem polynomial_preparedDraw : PolynomialTime preparedDrawRealizer :=
  polynomial_composition (polynomial_pair polynomial_drawIndices polynomial_identity)
    polynomial_permuteDrawData

def normalizedDraw (z : DenseDrawData) : MatrixCode := denseDrawCode (preparedDraw z)

def normalizedDrawRealizer : Realizer normalizedDraw :=
  composition preparedDrawRealizer denseDrawCodeRealizer

theorem polynomial_normalizedDraw : PolynomialTime normalizedDrawRealizer :=
  polynomial_composition polynomial_preparedDraw polynomial_denseDrawCode

def normalizedDenseCode (z : DenseDrawData) : MatrixCode :=
  swapMatrix (drawIndices z,normalizedDraw z)

def normalizedDenseCodeRealizer : Realizer normalizedDenseCode :=
  composition (pair drawIndicesRealizer normalizedDrawRealizer) swapMatrixRealizer

/-- Maximal-margin selection, forward permutation, the full dense draw,
and the inverse permutation all have polynomial binary cost. -/
theorem polynomial_normalizedDenseCode : PolynomialTime normalizedDenseCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_drawIndices polynomial_normalizedDraw)
    polynomial_swapMatrix

end ContingencyTables.DensePrograms

end OAI
