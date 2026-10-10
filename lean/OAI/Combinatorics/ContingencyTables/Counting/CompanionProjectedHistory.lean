import OAI.Combinatorics.ContingencyTables.Counting.CompanionHistoryReadback
import OAI.Combinatorics.ContingencyTables.Transport.FiniteBoundedProjectedHistory

namespace OAI

/-! # Lifting executed phase laws through the complete adaptive history -/
namespace ContingencyTables.CompanionProjectedHistory
open MatchingFPRAS CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionStoredRepresentation
open CompanionCanonicalHistory
open scoped Classical
noncomputable section

abbrev Stored := CompanionPhaseFinishProgram.Stored

def advance (fixed : CompanionOuterHistoryProgram.Fixed) {W : ℕ}
    (history : List Stored) (bits : Fin W→Bool) : List Stored :=
  history++[CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits)]

lemma fold_eq (fixed : CompanionOuterHistoryProgram.Fixed) {W : ℕ}
    (words : List (Fin W→Bool)) (history : List Stored) :
    ((words.map List.ofFn).foldl
      (fun state bits => CompanionOuterHistoryProgram.advance (bits,state)) (fixed,history))=
      (fixed,words.foldl (advance fixed) history) := by
  induction words generalizing history with
  | nil => rfl
  | cons word words ih =>
    simpa only [List.map_cons,List.foldl_cons,advance,CompanionOuterHistoryProgram.advance,
      CompanionOuterHistoryProgram.next,CompanionOuterHistoryProgram.phaseInput] using
      ih (advance fixed history word)

lemma storedHistory_eq (fixed : CompanionOuterHistoryProgram.Fixed) {W : ℕ}
    (words : List (Fin W→Bool)) :
    CompanionOuterHistoryProgram.storedHistory (fixed,words.map List.ofFn)=
      words.foldl (advance fixed) [] := by
  exact congrArg Prod.snd (fold_eq fixed words [])

lemma fold_length (fixed : CompanionOuterHistoryProgram.Fixed) {W : ℕ}
    (words : List (Fin W→Bool)) (history : List Stored) :
    (words.foldl (advance fixed) history).length=history.length+words.length := by
  induction words generalizing history with
  | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero]
  | cons word words ih =>
    rw [List.foldl_cons,ih]
    simp only [advance,List.length_append,List.length_cons,List.length_nil,List.length_cons]
    omega

variable {I J : Type} [Fintype I] [Fintype J]

theorem history_sameLaw (A : Instance I J) {p W : ℕ} (g : Fin p ≃ Labels A)
    (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (fixed : CompanionOuterHistoryProgram.Fixed)
    (hrep : ∀ history : List Stored,(∀ x∈history,StoredRep p x)→history.length<s.H→
      ∀ bits : Fin W→Bool,StoredRep p (CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits)))
    (hstep : ∀ history : List Stored,(∀ x∈history,StoredRep p x)→history.length<s.H→
      SameLaw (fun bits : Fin W→Bool => CompanionPhaseFinishProgram.view (p := p)
        (CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits)))
        (canonicalStep A g R s (history.map (CompanionPhaseFinishProgram.view (p := p))))) :
    SameLaw (fun words : Fin s.H→(Fin W→Bool) =>
      (CompanionOuterHistoryProgram.storedHistory
        (fixed,(List.ofFn words).map List.ofFn)).map (CompanionPhaseFinishProgram.view (p := p)))
      (fun words : Fin s.H→RootedPhaseHistory.Word A s =>
        canonicalDecoded A g R s (List.ofFn words)) := by
  let F : List Stored→(Fin W→Bool)→List Stored := advance fixed
  let G := canonicalAdvance A g R s
  let e := List.map (CompanionPhaseFinishProgram.view (p := p))
  let Valid := fun history : List Stored => ∀ x∈history,StoredRep p x
  have hv : ∀ history,Valid history→history.length<s.H→∀ bits,Valid (F history bits) := by
    intro history hh hlt bits x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hh x hx
    · have he : x=CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits) := by
        simpa only [List.mem_singleton] using hx
      subst x
      exact hrep history hh hlt bits
  have hs : ∀ history,Valid history→history.length<s.H→
      SameLaw (fun bits => e (F history bits)) (G (e history)) := by
    intro history hh hlt
    have h := (hstep history hh hlt).map (fun x => e history++[x])
    intro phi
    simpa only [e,F,G,advance,canonicalAdvance,List.map_append,List.map_singleton] using h phi
  have h := bounded_projected_foldl_sameLaw F G e Valid List.length s.H
    (fun history bits => by simp only [F,advance,List.length_append,List.length_cons,List.length_nil])
    hv hs [] (by simp [Valid]) s.H (by simp)
  intro phi
  simpa only [storedHistory_eq,e,F,G,canonicalDecoded,List.map_nil] using h phi

theorem output_sameLaw (A : Instance I J) {p W : ℕ} (g : Fin p ≃ Labels A)
    (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (fixed : CompanionOuterHistoryProgram.Fixed)
    (hinit : CompanionPhaseFinishProgram.view (p := p) fixed.2=
      project A g (RootedStoredEstimate.initialStored A))
    (hrep : ∀ history : List Stored,(∀ x∈history,StoredRep p x)→history.length<s.H→
      ∀ bits : Fin W→Bool,StoredRep p (CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits)))
    (hstep : ∀ history : List Stored,(∀ x∈history,StoredRep p x)→history.length<s.H→
      SameLaw (fun bits : Fin W→Bool => CompanionPhaseFinishProgram.view (p := p)
        (CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits)))
        (canonicalStep A g R s (history.map (CompanionPhaseFinishProgram.view (p := p))))) :
    SameLaw (fun words : Fin s.H→(Fin W→Bool) =>
      TreeFraction.val (CompanionOuterHistoryProgram.output
        (fixed,(List.ofFn words).map List.ofFn)).2)
      (RootedCountingWords.estimate A R s) := by
  have h := (history_sameLaw A g R s fixed hrep hstep).map
    (fun history => (canonicalLookup A g history s.H).2)
  have he (words : Fin s.H→(Fin W→Bool)) :
      TreeFraction.val (CompanionOuterHistoryProgram.output
        (fixed,(List.ofFn words).map List.ofFn)).2=
      (canonicalLookup A g
        ((CompanionOuterHistoryProgram.storedHistory
          (fixed,(List.ofFn words).map List.ofFn)).map (CompanionPhaseFinishProgram.view (p := p))) s.H).2 := by
    change (CompanionPhaseFinishProgram.view (p := p)
      (CompanionOuterPhaseProgram.old ((fixed,
        CompanionOuterHistoryProgram.storedHistory (fixed,(List.ofFn words).map List.ofFn)),[]))).2=_
    have hh := CompanionHistoryReadback.view_old_canonical A g fixed
      (CompanionOuterHistoryProgram.storedHistory (fixed,(List.ofFn words).map List.ofFn)) [] hinit
    have hl : (CompanionOuterHistoryProgram.storedHistory
        (fixed,(List.ofFn words).map List.ofFn)).length=s.H := by
      rw [storedHistory_eq,fold_length]
      simp only [List.length_nil,List.length_ofFn,Nat.zero_add]
    rw [hh,hl]
  intro phi
  simp_rw [he]
  exact (h phi).trans (by
    apply congrArg uniformAverage
    funext words
    rw [estimate_project]
    rfl)

end
end ContingencyTables.CompanionProjectedHistory

end OAI
