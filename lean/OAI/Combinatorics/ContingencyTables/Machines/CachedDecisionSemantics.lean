import OAI.Combinatorics.ContingencyTables.Machines.CachedProfileDecision

namespace OAI

/-! # Cached completions implement the same outer-profile transition -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

def encodedShortStep (h : ℕ) (x : PaperStates r c) (word : Fin s → Bool) : ShortStep :=
  (((stateCodeData r c e x,d^12),(d,h)),List.ofFn word)

/-- This identity holds for every feasible cached completion, including
those not selected by a particular finite random word. -/
theorem cachedDecision_encoded (htotal : ∑ i,r i=∑ j,c j) (h : ℕ)
    (x : PaperStates r c) (word : Fin s → Bool) (A : Table (R x) (P x)) :
    cachedDecision (encodedShortStep r c e h x word,tableOutput A)=
      stateCode r c e (completionDecision R P x (decodedCodeProposal r c e x word) A) := by
  have hp := codeProposal_encoded r c e htotal x word
  cases hd : decodedCodeProposal r c e x word with
  | none =>
    rw [hd,Option.map_none] at hp
    have hviews : stepCandidateViews (shortStepInput (encodedShortStep r c e h x word))=
        stateCode r c e x := by
      simp only [stepCandidateViews,stepProposal,shortStepInput,encodedShortStep,hp,
        Option.getD_none]
      rfl
    unfold cachedDecision
    rw [hviews]
    split_ifs <;> rfl
  | some y =>
    rw [hd,Option.map_some] at hp
    have hparams : stepCandidateParameters (shortStepInput (encodedShortStep r c e h x word))=
        ((stateCodeData r c e y,d^12),(d,h)) := by
      simp only [stepCandidateParameters,stepCandidate,stepCandidateViews,stepProposal,
        shortStepInput,encodedShortStep,hp,Option.getD_some]
      rfl
    have hdata : cachedDecisionInput (encodedShortStep r c e h x word,tableOutput A)=
        (((marginCode (R x),marginCode (P x)),(marginCode (R y),marginCode (P y))),
          tableOutput A) := by
      unfold cachedDecisionInput stepOldMargins stepNewMargins
      rw [hparams]
      dsimp only [shortStepInput,encodedShortStep]
      rw [residualParameters_code,residualParameters_code]
    have hviews : stepCandidateViews (shortStepInput (encodedShortStep r c e h x word))=
        stateCode r c e y := by
      simp only [stepCandidateViews,stepProposal,shortStepInput,encodedShortStep,hp,
        Option.getD_some]
    have hv := translationValid_code (R x) (R y) (P x) (P y) A
    unfold cachedDecision
    rw [hdata,hviews]
    change (if translationValid _ then stateCode r c e y else stateCode r c e x)=
      stateCode r c e (if ∀ i j,0 ≤ (A.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
        then y else x)
    by_cases ht : ∀ i j,0 ≤ (A.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
    · rw [ite_eq_left ht,ite_eq_left (hv.mpr ht)]
    · rw [ite_eq_right ht,ite_eq_right (fun hv' => ht (hv.mp hv'))]

end
end ContingencyTables.SmallGraphProfiles

end OAI
