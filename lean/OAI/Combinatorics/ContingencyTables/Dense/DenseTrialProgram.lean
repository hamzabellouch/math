import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanWalkProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseOffsetWidths
import OAI.Combinatorics.ContingencyTables.Dense.DenseCompletedMatrixProgram

namespace OAI

/-! # The complete dense trial as a polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

abbrev DenseTrialData := (FlatExponentData×ℕ)×List Bool

def fiftiethPower : Realizer (fun n : ℕ => n^50) :=
  (composition (composition fifthPower squareNat) fifthPower).congr (by
    intro n
    simp only [Function.comp_apply]
    ring)

theorem polynomial_fiftiethPower : PolynomialTime fiftiethPower :=
  polynomial_congr _ (polynomial_composition
    (polynomial_composition polynomial_fifthPower polynomial_squareNat) polynomial_fifthPower)

def trialWalkBits (z : DenseTrialData) : ℕ :=
  (z.1.1.2^50*(z.1.2+1)^2)*GridBoundary.denseStepBits z.1.1.2

def trialWalkBitsRealizer : Realizer trialWalkBits := by
  let D : Realizer (fun z : DenseTrialData => z.1.1.2) :=
    composition (composition first first) second
  let H : Realizer (fun z : DenseTrialData => z.1.2) := composition first second
  let time := composition (pair (composition D fiftiethPower)
    (composition (composition H successor) squareNat)) multiply
  exact (composition (pair time (composition D denseWidthRealizer)) multiply).congr (by
    intro z
    simp only [Function.comp_apply,trialWalkBits,pow_two,Nat.succ_eq_add_one])

theorem polynomial_trialWalkBits : PolynomialTime trialWalkBitsRealizer := by
  have hd : PolynomialTime (composition
      (composition (first (A := FlatExponentData×ℕ) (B := List Bool)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  unfold trialWalkBitsRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_composition hd polynomial_fiftiethPower)
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_second) polynomial_successor)
        polynomial_squareNat)) polynomial_multiply)
    (polynomial_composition hd polynomial_denseWidth)) polynomial_multiply

def trialGrid (z : DenseTrialData) : ExponentData :=
  flatToGridData (flatWordWalk (z.1.1,z.2.take (trialWalkBits z)))

def trialGridRealizer : Realizer trialGrid := by
  let data : Realizer (fun z : DenseTrialData => z.1.1) := composition first first
  let bits := composition (pair (second (A := FlatExponentData×ℕ) (B := List Bool))
    trialWalkBitsRealizer) takeFast
  let source := pair data bits
  let walk := composition source flatWordWalkRealizer
  let result := composition walk flatToGridDataRealizer
  exact result

theorem polynomial_trialGrid : PolynomialTime trialGridRealizer := by
  unfold trialGridRealizer
  exact polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_trialWalkBits) polynomial_takeFast))
    polynomial_flatWordWalk) polynomial_flatToGridData

def trialOffsets (z : DenseTrialData) : List (List Bool) :=
  dependentChunks (offsetLengths (trialGrid z,z.1.2),z.2.drop (trialWalkBits z))

def trialOffsetsRealizer : Realizer trialOffsets :=
  composition (pair
    (composition (pair trialGridRealizer (composition first second)) offsetLengthsRealizer)
    (composition (pair second trialWalkBitsRealizer) dropFast)) dependentChunksRealizer

theorem polynomial_trialOffsets : PolynomialTime trialOffsetsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_trialGrid
      (polynomial_composition polynomial_first polynomial_second)) polynomial_offsetLengths)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_trialWalkBits) polynomial_dropFast))
    polynomial_dependentChunks

def trialCompletion (z : DenseTrialData) : CompletionData :=
  ((trialGrid z).1.1,offsetMatrix (trialGrid z,trialOffsets z))

def trialCompletionRealizer : Realizer trialCompletion :=
  pair (composition (composition trialGridRealizer first) first)
    (composition (pair trialGridRealizer trialOffsetsRealizer) offsetMatrixRealizer)

theorem polynomial_trialCompletion : PolynomialTime trialCompletionRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition polynomial_trialGrid polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_trialGrid polynomial_trialOffsets) polynomial_offsetMatrix)

def acceptCompletion (z : CompletionData) : Option MatrixCode :=
  if completionValid z then some (completedMatrix z) else none

def acceptCompletionRealizer : Realizer acceptCompletion :=
  choose completionValidRealizer (composition completedMatrixRealizer MatchingFPRAS.TreeTyped.some) (constant none)

theorem polynomial_acceptCompletion : PolynomialTime acceptCompletionRealizer :=
  polynomial_choose polynomial_completionValid
    (polynomial_composition polynomial_completedMatrix polynomial_some) (polynomial_constant none)

def denseTrialCode (z : DenseTrialData) : Option MatrixCode := acceptCompletion (trialCompletion z)

def denseTrialCodeRealizer : Realizer denseTrialCode :=
  composition trialCompletionRealizer acceptCompletionRealizer

/-- Includes the full walk, every quotient offset, signed-entry checking,
and binary output construction. Runtime is polynomial for every input. -/
theorem polynomial_denseTrialCode : PolynomialTime denseTrialCodeRealizer :=
  polynomial_composition polynomial_trialCompletion polynomial_acceptCompletion

end ContingencyTables.DensePrograms

end OAI
