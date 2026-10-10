import OAI.Combinatorics.ContingencyTables.Transport.BoundedProfileWalk
import OAI.Combinatorics.ContingencyTables.Sampling.OuterTrialProgram

namespace OAI

/-! # A complete polynomial outer trial on supplied independent words -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev ProfileTrialData := (ProfileConfiguration×List ProfileWord)×List Bool

def trialState (z : ProfileTrialData) : ProfileConfiguration := profileWalk z.1
def trialStateRealizer : Realizer trialState := composition first profileWalkRealizer

theorem polynomial_trialState : PolynomialTime trialStateRealizer :=
  polynomial_composition polynomial_first polynomial_profileWalk

def trialParameters (z : ProfileTrialData) : ResidualParameters := currentParameters (trialState z)
def trialParametersRealizer : Realizer trialParameters :=
  composition trialStateRealizer currentParametersRealizer

theorem polynomial_trialParameters : PolynomialTime trialParametersRealizer :=
  polynomial_composition polynomial_trialState polynomial_currentParameters

def trialCompletion (z : ProfileTrialData) : DensePrograms.MatrixCode :=
  reservedResidualDraw (trialParameters z,z.2)
def trialCompletionRealizer : Realizer trialCompletion :=
  composition (pair trialParametersRealizer second) reservedResidualDrawRealizer

theorem polynomial_trialCompletion : PolynomialTime trialCompletionRealizer :=
  polynomial_composition (polynomial_pair polynomial_trialParameters polynomial_second)
    polynomial_reservedResidualDraw

def trialOutputInput (z : ProfileTrialData) : OuterTrialInput :=
  ((trialParameters z).1,trialCompletion z)
def trialOutputInputRealizer : Realizer trialOutputInput :=
  pair (composition trialParametersRealizer first) trialCompletionRealizer

theorem polynomial_trialOutputInput : PolynomialTime trialOutputInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_trialParameters polynomial_first)
    polynomial_trialCompletion

def profileTrial (z : ProfileTrialData) : Option DensePrograms.MatrixCode :=
  outerTrial (trialOutputInput z)
def profileTrialRealizer : Realizer profileTrial :=
  composition trialOutputInputRealizer outerTrialRealizer

theorem polynomial_profileTrial : PolynomialTime profileTrialRealizer :=
  polynomial_composition polynomial_trialOutputInput polynomial_outerTrial

end ContingencyTables.ProfilePrograms

end OAI
