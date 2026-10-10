import OAI.Combinatorics.ContingencyTables.Transport.ListedReservedDraw
import OAI.Combinatorics.ContingencyTables.Transport.TranslationDecisionSemantics
import OAI.Combinatorics.ContingencyTables.Machines.FirstSuccessProgram

namespace OAI

/-! # A binary small-profile transition with a fresh dense completion -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev ProfileStepInput := ResidualParameters×(List Bool×List Bool)

def stepCheck : Realizer (fun z : ProfileStepInput => z.1.1.1) :=
  composition (composition first first) first

theorem polynomial_stepCheck : PolynomialTime stepCheck :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first

def stepViews : Realizer (fun z : ProfileStepInput => z.1.1.1.1.1.2) :=
  composition (f := fun z : ProfileStepInput => z.1.1.1)
    (g := fun z : ProfileCheckData => z.1.1.2) stepCheck profileViews

theorem polynomial_stepViews : PolynomialTime stepViews :=
  polynomial_composition polynomial_stepCheck polynomial_profileViews

def stepProposal (z : ProfileStepInput) : Option (List ℕ×List ℕ) :=
  codeNeighborProposal (z.1.1.1,z.2.1)

def stepProposalRealizer : Realizer stepProposal :=
  composition (pair stepCheck (composition second first)) codeNeighborProposalRealizer

theorem polynomial_stepProposal : PolynomialTime stepProposalRealizer :=
  polynomial_composition (polynomial_pair polynomial_stepCheck
    (polynomial_composition polynomial_second polynomial_first)) polynomial_codeNeighborProposal

def stepCandidateViews (z : ProfileStepInput) : List ℕ×List ℕ :=
  (stepProposal z).getD z.1.1.1.1.1.2

def stepCandidateViewsRealizer : Realizer stepCandidateViews :=
  composition (pair stepViews stepProposalRealizer) FirstSuccessProgram.defaultRealizer

theorem polynomial_stepCandidateViews : PolynomialTime stepCandidateViewsRealizer :=
  polynomial_composition (polynomial_pair polynomial_stepViews polynomial_stepProposal)
    FirstSuccessProgram.polynomial_default

def stepCandidate (z : ProfileStepInput) : ProfileCheckData :=
  candidateData (z.1.1.1,stepCandidateViews z)

def stepCandidateRealizer : Realizer stepCandidate :=
  composition (pair stepCheck stepCandidateViewsRealizer) candidateDataRealizer

theorem polynomial_stepCandidate : PolynomialTime stepCandidateRealizer :=
  polynomial_composition (polynomial_pair polynomial_stepCheck polynomial_stepCandidateViews)
    polynomial_candidateData

def stepCandidateParameters (z : ProfileStepInput) : ResidualParameters :=
  ((stepCandidate z,z.1.1.2),z.1.2)

def stepCandidateParametersRealizer : Realizer stepCandidateParameters :=
  pair (pair stepCandidateRealizer (composition (composition first first) second))
    (composition first second)

theorem polynomial_stepCandidateParameters : PolynomialTime stepCandidateParametersRealizer :=
  polynomial_pair (polynomial_pair polynomial_stepCandidate
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
    (polynomial_composition polynomial_first polynomial_second)

def stepOldMargins (z : ProfileStepInput) : DensePrograms.MarginPair :=
  (residualParameters z.1).1

def stepOldMarginsRealizer : Realizer stepOldMargins :=
  composition (f := fun z : ProfileStepInput => residualParameters z.1)
    (g := fun z : DensePrograms.CanonicalParameters => z.1)
    (composition (f := fun z : ProfileStepInput => z.1) (g := residualParameters)
      first residualParametersRealizer) first

theorem polynomial_stepOldMargins : PolynomialTime stepOldMarginsRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_residualParameters)
    polynomial_first

def stepNewMargins (z : ProfileStepInput) : DensePrograms.MarginPair :=
  (residualParameters (stepCandidateParameters z)).1

def stepNewMarginsRealizer : Realizer stepNewMargins :=
  composition (f := fun z : ProfileStepInput => residualParameters (stepCandidateParameters z))
    (g := fun z : DensePrograms.CanonicalParameters => z.1)
    (composition (f := stepCandidateParameters) (g := residualParameters)
      stepCandidateParametersRealizer residualParametersRealizer) first

theorem polynomial_stepNewMargins : PolynomialTime stepNewMarginsRealizer :=
  polynomial_composition (polynomial_composition polynomial_stepCandidateParameters
    polynomial_residualParameters) polynomial_first

def stepCompletion (z : ProfileStepInput) : DensePrograms.MatrixCode :=
  reservedResidualDraw (z.1,z.2.2)

def stepCompletionRealizer : Realizer stepCompletion :=
  composition (f := fun z : ProfileStepInput => (z.1,z.2.2))
    (g := reservedResidualDraw) (pair first (composition second second)) reservedResidualDrawRealizer

theorem polynomial_stepCompletion : PolynomialTime stepCompletionRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_second)) polynomial_reservedResidualDraw

def stepTranslation (z : ProfileStepInput) : DensePrograms.TranslationData :=
  ((stepOldMargins z,stepNewMargins z),stepCompletion z)

def stepTranslationRealizer : Realizer stepTranslation :=
  pair (pair stepOldMarginsRealizer stepNewMarginsRealizer) stepCompletionRealizer

theorem polynomial_stepTranslation : PolynomialTime stepTranslationRealizer :=
  polynomial_pair (polynomial_pair polynomial_stepOldMargins polynomial_stepNewMargins)
    polynomial_stepCompletion

def profileStep (z : ProfileStepInput) : List ℕ×List ℕ :=
  if DensePrograms.translationValid (stepTranslation z) then stepCandidateViews z else z.1.1.1.1.1.2

def profileStepRealizer : Realizer profileStep :=
  (choose (composition stepTranslationRealizer DensePrograms.translationValidRealizer)
    stepCandidateViewsRealizer stepViews).congr
    (by intro z; simp only [profileStep,Function.comp_apply])

theorem polynomial_profileStep : PolynomialTime profileStepRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition polynomial_stepTranslation DensePrograms.polynomial_translationValid)
    polynomial_stepCandidateViews polynomial_stepViews)

end ContingencyTables.ProfilePrograms

end OAI
