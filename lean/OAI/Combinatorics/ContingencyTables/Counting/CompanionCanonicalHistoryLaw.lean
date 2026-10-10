import OAI.Combinatorics.ContingencyTables.Counting.CompanionCanonicalHistory
import OAI.Combinatorics.ContingencyTables.Transport.FiniteProjectedHistory
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCountingWords

namespace OAI

/-! # The complete source estimator factors through canonical stored entries -/
namespace ContingencyTables.CompanionCanonicalHistory
open CompanionFactorialApplication CommonBasesFPRAS GridBoundary FiniteObservableTransport
open CompanionPhaseWords (Stored)
open scoped Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)

def sourceAdvance (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Stored A)) (bits : RootedPhaseHistory.Word A s) : List (Stored A) :=
  history++[RootedPhaseHistory.step A R s history bits]

def canonicalAdvance (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Canonical (p := p))) (bits : RootedPhaseHistory.Word A s) : List (Canonical (p := p)) :=
  history++[canonicalStep A g R s history bits]

lemma advance_project (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Stored A)) (bits : RootedPhaseHistory.Word A s) :
    (sourceAdvance A R s history bits).map (project A g)=
      canonicalAdvance A g R s (history.map (project A g)) bits := by
  simp only [sourceAdvance,canonicalAdvance,List.map_append,List.map_singleton,step_project]

lemma fold_project (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (words : List (RootedPhaseHistory.Word A s)) (history : List (Stored A)) :
    (words.foldl (sourceAdvance A R s) history).map (project A g)=
      words.foldl (canonicalAdvance A g R s) (history.map (project A g)) := by
  induction words generalizing history with
  | nil => rfl
  | cons word words ih =>
    rw [List.foldl_cons,List.foldl_cons,ih,advance_project]

def canonicalDecoded (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (words : List (RootedPhaseHistory.Word A s)) : List (Canonical (p := p)) :=
  words.foldl (canonicalAdvance A g R s) []

theorem decoded_project (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (words : List (RootedPhaseHistory.Word A s)) :
    (RootedPhaseHistory.decoded A R s words).map (project A g)=canonicalDecoded A g R s words :=
  fold_project A g R s words []

theorem decoded_sameLaw (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (N : ℕ) :
    SameLaw (fun words : Fin N→RootedPhaseHistory.Word A s =>
      (RootedPhaseHistory.decoded A R s (List.ofFn words)).map (project A g))
      (fun words : Fin N→RootedPhaseHistory.Word A s => canonicalDecoded A g R s (List.ofFn words)) := by
  apply projected_foldl_sameLaw (sourceAdvance A R s) (canonicalAdvance A g R s)
    (List.map (project A g)) (fun _ => True) (fun _ _ _ => trivial) ?_ [] trivial N
  intro history _ phi
  apply congrArg uniformAverage
  funext bits
  change phi ((sourceAdvance A R s history bits).map (project A g)) = _
  rw [advance_project]

def canonicalLookup (history : List (Canonical (p := p))) : ℕ→Canonical (p := p)
  | 0 => project A g (RootedStoredEstimate.initialStored A)
  | i+1 => history.getD i (project A g (RootedStoredEstimate.initialStored A))

lemma lookup_project (history : List (Stored A)) (i : ℕ) :
    project A g (RootedStoredHistory.lookup A history i)=
      canonicalLookup A g (history.map (project A g)) i := by
  cases i with
  | zero => rfl
  | succ i => exact (List.getD_map history (RootedStoredEstimate.initialStored A)
      (project A g)).symm

def canonicalEstimate (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (words : Fin s.H→RootedPhaseHistory.Word A s) : ℚ :=
  (canonicalLookup A g (canonicalDecoded A g R s (List.ofFn words)) s.H).2

theorem estimate_project (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (words : Fin s.H→RootedPhaseHistory.Word A s) :
    RootedCountingWords.estimate A R s words=canonicalEstimate A g R s words := by
  change (project A g (RootedStoredHistory.lookup A
    (RootedPhaseHistory.decoded A R s (List.ofFn words)) s.H)).2=_
  rw [lookup_project,decoded_project]
  rfl

theorem estimate_sameLaw (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A) :
    SameLaw (RootedCountingWords.estimate A R s) (canonicalEstimate A g R s) := by
  intro phi
  apply congrArg uniformAverage
  funext words
  rw [estimate_project]

theorem flatEstimate_sameLaw (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A) :
    SameLaw (RootedCountingWords.flatEstimate A R s) (canonicalEstimate A g R s) := by
  intro phi
  have h := uniformAverage_equiv (gridWordEquiv s.H (RootedPhaseHistory.totalWidth A s))
    (fun words => phi (RootedCountingWords.estimate A R s words))
  exact h.trans (estimate_sameLaw A g R s phi)

end
end ContingencyTables.CompanionCanonicalHistory

end OAI
