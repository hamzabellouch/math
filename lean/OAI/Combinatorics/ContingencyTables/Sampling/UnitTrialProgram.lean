import OAI.Combinatorics.ContingencyTables.Sampling.UnitProfileProgram

namespace OAI

/-! # All-small trials and retries use only the stored profile entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def unitPackedWords (z : PackedProfileTrial) : List (List Bool) :=
  wordChunks (z.1.2.1.2,z.2)
def unitPackedWordsRealizer : Realizer unitPackedWords :=
  composition (f := fun z : PackedProfileTrial => (z.1.2.1.2,z.2)) (g := wordChunks)
    (pair (composition (composition (composition first second) first) second) second) wordChunksRealizer

theorem polynomial_unitPackedWords : PolynomialTime unitPackedWordsRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
    polynomial_second) polynomial_second) polynomial_wordChunks

def unitPackedState (z : PackedProfileTrial) : ProfileConfiguration :=
  unitProfileWalk (z.1.1,unitPackedWords z)
def unitPackedStateRealizer : Realizer unitPackedState :=
  composition (f := fun z : PackedProfileTrial => (z.1.1,unitPackedWords z)) (g := unitProfileWalk)
    (pair (composition first first) unitPackedWordsRealizer) unitProfileWalkRealizer

theorem polynomial_unitPackedState : PolynomialTime unitPackedStateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    polynomial_unitPackedWords) polynomial_unitProfileWalk

def unitPackedTrial (z : PackedProfileTrial) : Option MatrixCode :=
  outerTrial ((currentParameters (unitPackedState z)).1,[])
def unitPackedTrialRealizer : Realizer unitPackedTrial :=
  composition (f := fun z : PackedProfileTrial => ((currentParameters (unitPackedState z)).1,[]))
    (g := outerTrial) (pair
      (composition (f := fun z : PackedProfileTrial => currentParameters (unitPackedState z))
        (g := Prod.fst) (composition (f := unitPackedState) (g := currentParameters)
          unitPackedStateRealizer currentParametersRealizer) first) (constant [])) outerTrialRealizer

theorem polynomial_unitPackedTrial : PolynomialTime unitPackedTrialRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_unitPackedState polynomial_currentParameters) polynomial_first)
    (polynomial_constant [])) polynomial_outerTrial

def unitRetryWidth (z : ProfileRetryData) : ℕ := z.1.1.2.1.1*z.1.1.2.1.2
def unitRetryWidthRealizer : Realizer unitRetryWidth :=
  composition (f := fun z : ProfileRetryData => (z.1.1.2.1.1,z.1.1.2.1.2))
    (g := fun t : ℕ×ℕ => t.1*t.2)
    (pair (composition (composition (composition (composition first first) second) first) first)
      (composition (composition (composition (composition first first) second) first) second)) multiply

theorem polynomial_unitRetryWidth : PolynomialTime unitRetryWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
      polynomial_second)) polynomial_multiply

def unitRetryWords (z : ProfileRetryData) : List (List Bool) := wordChunks (unitRetryWidth z,z.2)
def unitRetryWordsRealizer : Realizer unitRetryWords :=
  composition (f := fun z : ProfileRetryData => (unitRetryWidth z,z.2)) (g := wordChunks)
    (pair unitRetryWidthRealizer second) wordChunksRealizer

theorem polynomial_unitRetryWords : PolynomialTime unitRetryWordsRealizer :=
  polynomial_composition (polynomial_pair polynomial_unitRetryWidth polynomial_second) polynomial_wordChunks

def unitProfileRetry (z : ProfileRetryData) : MatrixCode :=
  FirstSuccessProgram.retry unitPackedTrial (z.1,unitRetryWords z)
def unitProfileRetryRealizer : Realizer unitProfileRetry :=
  composition (f := fun z : ProfileRetryData => (z.1,unitRetryWords z))
    (g := FirstSuccessProgram.retry unitPackedTrial) (pair first unitRetryWordsRealizer)
    (FirstSuccessProgram.retryRealizer unitPackedTrialRealizer)

theorem polynomial_unitProfileRetry : PolynomialTime unitProfileRetryRealizer :=
  polynomial_composition (polynomial_pair polynomial_first polynomial_unitRetryWords)
    (FirstSuccessProgram.polynomial_retry polynomial_unitPackedTrial)

end ContingencyTables.ProfilePrograms

end OAI
