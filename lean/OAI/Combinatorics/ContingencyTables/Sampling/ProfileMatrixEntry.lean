import OAI.Combinatorics.ContingencyTables.Machines.TransitionCacheRuntime
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileBoxEnumeration

namespace OAI

/-! # Executable entries of the finite profile transition matrix -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev MatrixParameters := TransitionCacheParameters×List Bool
abbrev MatrixEntryInput := MatrixParameters×((List ℕ×List ℕ)×(List ℕ×List ℕ))

def matrixData (z : MatrixParameters) : ProfileCheckData := z.1.1.1.1

def matrixDataRealizer : Realizer matrixData :=
  composition (composition (composition first first) first) first

lemma polynomial_matrixData : PolynomialTime matrixDataRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first

def sourceData (z : MatrixEntryInput) : ProfileCheckData :=
  candidateData (matrixData z.1,z.2.1)

def sourceDataRealizer : Realizer sourceData :=
  composition (pair (composition (f := fun z : MatrixEntryInput => z.1) (g := matrixData) first matrixDataRealizer) (composition second first))
    candidateDataRealizer

lemma polynomial_sourceData : PolynomialTime sourceDataRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_matrixData)
    (polynomial_composition polynomial_second polynomial_first)) polynomial_candidateData

def targetData (z : MatrixEntryInput) : ProfileCheckData :=
  candidateData (matrixData z.1,z.2.2)

def targetDataRealizer : Realizer targetData :=
  composition (pair (composition (f := fun z : MatrixEntryInput => z.1) (g := matrixData) first matrixDataRealizer) (composition second second))
    candidateDataRealizer

lemma polynomial_targetData : PolynomialTime targetDataRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_matrixData)
    (polynomial_composition polynomial_second polynomial_second)) polynomial_candidateData

def entryCacheParameters (z : MatrixEntryInput) : TransitionCacheParameters :=
  (((sourceData z,z.1.1.1.1.2),z.1.1.1.2),z.1.1.2)

def entryCacheParametersRealizer : Realizer entryCacheParameters := by
  let params : Realizer (fun z : MatrixEntryInput => z.1.1) := composition first first
  let resid : Realizer (fun z : MatrixEntryInput => z.1.1.1) := composition params first
  let padding := composition (composition resid first) second
  exact pair (pair (pair sourceDataRealizer padding) (composition resid second))
    (composition params second)

lemma polynomial_entryCacheParameters : PolynomialTime entryCacheParametersRealizer := by
  unfold entryCacheParametersRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair polynomial_sourceData
    (polynomial_composition (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first) polynomial_first) polynomial_second))
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second))
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)

def entryQuery (z : MatrixEntryInput) : TransitionQuery :=
  ((prepareTransitionCache (entryCacheParameters z),z.2.2),z.1.2)

def entryQueryRealizer : Realizer entryQuery :=
  pair (pair
    (composition (f := entryCacheParameters) (g := prepareTransitionCache)
      entryCacheParametersRealizer prepareTransitionCacheRealizer)
    (composition second second)) (composition first second)

def validMatrixEntry (z : MatrixEntryInput) : ℕ := transitionCount (entryQuery z)

def validMatrixEntryRealizer : Realizer validMatrixEntry :=
  composition (f := entryQuery) (g := transitionCount) entryQueryRealizer transitionCountRealizer

/-- The denominator includes the proposal word and its padded completion word. -/
def matrixDenominator (z : MatrixParameters) : ℕ :=
  BinaryPowerPrograms.power (2,z.2.length+z.1.2)

def matrixDenominatorRealizer : Realizer matrixDenominator :=
  composition (pair (constant 2) (composition (pair
    (composition second listLength) (composition first second)) add)) BinaryPowerPrograms.powerRealizer

def diagonalMatrixEntry (z : MatrixEntryInput) : ℕ :=
  if z.2.1=z.2.2 then matrixDenominator z.1 else 0

def diagonalMatrixEntryRealizer : Realizer diagonalMatrixEntry :=
  (choose (composition second profileCodeEqual)
    (composition first matrixDenominatorRealizer) (constant 0)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq]
      rfl)

/-- Invalid source vectors are stationary. Invalid target vectors have
zero weight from every valid source. -/
def matrixEntry (z : MatrixEntryInput) : ℕ :=
  if profileTest (sourceData z) then
    if profileTest (targetData z) then validMatrixEntry z else 0
  else diagonalMatrixEntry z

def matrixEntryRealizer : Realizer matrixEntry :=
  choose (composition sourceDataRealizer profileTestRealizer)
    (choose (composition targetDataRealizer profileTestRealizer)
      validMatrixEntryRealizer (constant 0)) diagonalMatrixEntryRealizer

end ContingencyTables.ProfilePrograms

end OAI
