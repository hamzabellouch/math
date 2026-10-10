import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTransitionSemantics

namespace OAI

/-! # Reusing the outer transition test on an enumerated completion -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev ShortStep := ResidualParameters×List Bool

def shortStepInput (z : ShortStep) : ProfileStepInput := (z.1,(z.2,[]))

def shortStepInputRealizer : Realizer shortStepInput :=
  pair first (pair second (constant []))

lemma polynomial_shortStepInput : PolynomialTime shortStepInputRealizer :=
  polynomial_pair polynomial_first (polynomial_pair polynomial_second (polynomial_constant []))

def cachedDecisionInput (z : ShortStep×DensePrograms.MatrixCode) : DensePrograms.TranslationData :=
  ((stepOldMargins (shortStepInput z.1),stepNewMargins (shortStepInput z.1)),z.2)

def cachedDecisionInputRealizer : Realizer cachedDecisionInput := by
  let input := composition (first (A := ShortStep) (B := DensePrograms.MatrixCode))
    shortStepInputRealizer
  let old := composition input stepOldMarginsRealizer
  let next := composition input stepNewMarginsRealizer
  exact pair (pair old next) second

lemma polynomial_cachedDecisionInput : PolynomialTime cachedDecisionInputRealizer := by
  unfold cachedDecisionInputRealizer
  exact polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_shortStepInput)
      polynomial_stepOldMargins)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_shortStepInput)
      polynomial_stepNewMargins)) polynomial_second

def cachedDecision (z : ShortStep×DensePrograms.MatrixCode) : List ℕ×List ℕ :=
  if DensePrograms.translationValid (cachedDecisionInput z)
    then stepCandidateViews (shortStepInput z.1) else z.1.1.1.1.1.1.2

def cachedDecisionRealizer : Realizer cachedDecision := by
  let input := composition (first (A := ShortStep) (B := DensePrograms.MatrixCode))
    shortStepInputRealizer
  let yes := composition input stepCandidateViewsRealizer
  let no := composition input stepViews
  exact (choose (composition cachedDecisionInputRealizer DensePrograms.translationValidRealizer)
    yes no).congr (by intro z; rfl)

lemma polynomial_cachedDecision : PolynomialTime cachedDecisionRealizer := by
  unfold cachedDecisionRealizer
  exact polynomial_congr _ (polynomial_choose
    (polynomial_composition polynomial_cachedDecisionInput DensePrograms.polynomial_translationValid)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_shortStepInput)
      polynomial_stepCandidateViews)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_shortStepInput)
      polynomial_stepViews))

/-- Changing only the completion bits cannot change the selected proposal. -/
lemma shortStep_candidate (z : ProfileStepInput) :
    stepCandidateViews (shortStepInput (z.1,z.2.1))=stepCandidateViews z := rfl

/-- The exact test applied to a cached completion agrees with the
implemented transition when that completion was actually drawn. -/
lemma cachedDecision_actual (z : ProfileStepInput) :
    cachedDecision ((z.1,z.2.1),stepCompletion z)=profileStep z := rfl

end ContingencyTables.ProfilePrograms

end OAI
