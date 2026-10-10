import OAI.Combinatorics.ContingencyTables.Sampling.ProfileWordProgram
import OAI.Combinatorics.ContingencyTables.Machines.FirstSuccessProgram

namespace OAI

/-! # A polynomial retry loop for the complete binary outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

abbrev ProfileRetryParameters := (ProfileConfiguration×ProfileWordSchedule)×MatrixCode
abbrev ProfileRetryData := ProfileRetryParameters×List Bool

def profileTrialWidth (z : ProfileRetryData) : ℕ :=
  z.1.1.2.1.1*(z.1.1.2.1.2+z.1.1.2.2)+z.1.1.2.2

def profileRetryWordInput (z : ProfileRetryData) : ProfileWordInput := (z.1.1.2,z.2)
def profileRetryWordInputRealizer : Realizer profileRetryWordInput :=
  pair (composition (composition first first) second) second

theorem polynomial_profileRetryWordInput : PolynomialTime profileRetryWordInputRealizer :=
  polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second

def profileTrialWidthRealizer : Realizer profileTrialWidth :=
  composition (pair (composition profileRetryWordInputRealizer profileWalkWidthRealizer)
    (composition (composition (composition first first) second) second)) add

theorem polynomial_profileTrialWidth : PolynomialTime profileTrialWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_profileRetryWordInput polynomial_profileWalkWidth)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second))
    polynomial_add

def profileRetryWords (z : ProfileRetryData) : List (List Bool) :=
  wordChunks (profileTrialWidth z,z.2)
def profileRetryWordsRealizer : Realizer profileRetryWords :=
  composition (pair profileTrialWidthRealizer second) wordChunksRealizer

theorem polynomial_profileRetryWords : PolynomialTime profileRetryWordsRealizer :=
  polynomial_composition (polynomial_pair polynomial_profileTrialWidth polynomial_second)
    polynomial_wordChunks

def profileRetry (z : ProfileRetryData) : MatrixCode :=
  FirstSuccessProgram.retry packedProfileTrial (z.1,profileRetryWords z)
def profileRetryRealizer : Realizer profileRetry :=
  composition (pair first profileRetryWordsRealizer)
    (FirstSuccessProgram.retryRealizer packedProfileTrialRealizer)

theorem polynomial_profileRetry : PolynomialTime profileRetryRealizer :=
  polynomial_composition (polynomial_pair polynomial_first polynomial_profileRetryWords)
    (FirstSuccessProgram.polynomial_retry polynomial_packedProfileTrial)

end ContingencyTables.ProfilePrograms

end OAI
