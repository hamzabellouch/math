import OAI.Combinatorics.ContingencyTables.Dense.DenseTrialProgram
import OAI.Combinatorics.ContingencyTables.Machines.FirstSuccessProgram

namespace OAI

/-! # The bounded dense draw as a single polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

abbrev DenseDrawParameters := FlatExponentData×ℕ
abbrev DenseDrawData := (DenseDrawParameters×MatrixCode)×List Bool

def trialWidth (z : DenseDrawParameters) : ℕ :=
  trialWalkBits (z,[])+(offsetLengths (flatToGridData z.1,z.2)).sum

def trialWidthRealizer : Realizer trialWidth := by
  let blank : Realizer (fun z : DenseDrawParameters => (z,([] : List Bool))) :=
    pair identity (constant [])
  let widths := composition (pair (composition first flatToGridDataRealizer) second)
    offsetLengthsRealizer
  exact composition (pair (composition blank trialWalkBitsRealizer)
    (composition widths listSum)) add

theorem polynomial_trialWidth : PolynomialTime trialWidthRealizer := by
  unfold trialWidthRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant []))
      polynomial_trialWalkBits)
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_flatToGridData) polynomial_second)
      polynomial_offsetLengths) polynomial_listSum)) polynomial_add

def drawChunks (z : DenseDrawData) : List (List Bool) :=
  wordChunks (trialWidth z.1.1,z.2)

def drawChunksRealizer : Realizer drawChunks :=
  composition (pair (composition (composition first first) trialWidthRealizer) second)
    wordChunksRealizer

theorem polynomial_drawChunks : PolynomialTime drawChunksRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_trialWidth) polynomial_second) polynomial_wordChunks

def denseDrawCode (z : DenseDrawData) : MatrixCode :=
  FirstSuccessProgram.retry denseTrialCode (z.1,drawChunks z)

def denseDrawCodeRealizer : Realizer denseDrawCode :=
  composition (pair first drawChunksRealizer) (FirstSuccessProgram.retryRealizer denseTrialCodeRealizer)

/-- Every finite input has polynomial binary cost. On a valid dense input,
the first successful trial is selected, or the supplied feasible fallback. -/
theorem polynomial_denseDrawCode : PolynomialTime denseDrawCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_first polynomial_drawChunks)
    (FirstSuccessProgram.polynomial_retry polynomial_denseTrialCode)

end ContingencyTables.DensePrograms

end OAI
