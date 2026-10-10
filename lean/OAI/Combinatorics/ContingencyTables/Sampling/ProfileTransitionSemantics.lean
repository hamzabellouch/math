import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTransitionProgram
import OAI.Combinatorics.ContingencyTables.Transport.ListedReferenceDecision

namespace OAI

/-! # Exact semantics of the binary outer transition -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical

noncomputable section

private lemma apply_decision {X Y : Type*} (encode : X → Y) (x y : X)
    (test : Bool) (accept : Prop) [Decidable accept] (h : test=true ↔ accept) :
    (if test then encode y else encode x)=encode (if accept then y else x) := by
  by_cases hp : accept
  · rw [ite_eq_left hp,ite_eq_left (h.mpr hp)]
  · rw [ite_eq_right hp,ite_eq_right (fun ht => hp (h.mp ht))]

private lemma completionDecision_some_formula {X I J : Type*} [Fintype I] [Fintype J]
    (R : X → Option I → ℕ) (P : X → Option J → ℕ) (x y : X) (A : Table (R x) (P x)) :
    completionDecision R P x (some y) A=
      if ∀ i j,0 ≤ (A.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j then y else x := rfl

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))

theorem codeProposal_encoded (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c)
    (bits : Fin (smallProposalBits (I := Fin m) (J := Fin n)) → Bool) :
    codeNeighborProposal (stateCodeData r c e x,List.ofFn bits)=
      (decodedCodeProposal r c e x bits).map (stateCode r c e) := by
  cases hp : codeNeighborProposal (stateCodeData r c e x,List.ofFn bits) with
  | none => simp only [decodedCodeProposal,hp,Option.bind_none,Option.map_none]
  | some v =>
    have hv : v∈codeNeighbors (stateCodeData r c e x) := List.mem_of_getElem? hp
    obtain ⟨y,hy⟩ := codeNeighbors_decode_total r c e htotal x v hv
    have he := (decodeStateCode_eq_some_iff r c e v y).mp hy
    simp only [decodedCodeProposal,hp,Option.bind_some,hy,Option.map_some,he]

variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

def encodedStepInput (x : PaperStates r c) (proposal : Fin s → Bool) (completion : Fin f → Bool) :
    ProfileStepInput := (((stateCodeData r c e x,d^12),(d,h)),(List.ofFn proposal,List.ofFn completion))

lemma stepCandidate_encoded (x y : PaperStates r c) (proposal : Fin s → Bool) (completion : Fin f → Bool)
    (hp : codeNeighborProposal (stateCodeData r c e x,List.ofFn proposal)=some (stateCode r c e y)) :
    stepCandidateParameters (encodedStepInput r c e b h x proposal completion)=
      ((stateCodeData r c e y,d^12),(d,h)) := by
  simp only [stepCandidateParameters,stepCandidate,stepCandidateViews,stepProposal,encodedStepInput,hp,
    Option.getD_some]
  rfl

lemma stepTranslation_encoded (x y : PaperStates r c) (proposal : Fin s → Bool) (completion : Fin f → Bool)
    (hp : codeNeighborProposal (stateCodeData r c e x,List.ofFn proposal)=some (stateCode r c e y)) :
    stepTranslation (encodedStepInput r c e b h x proposal completion)=
      (((marginCode (R x),marginCode (P x)),(marginCode (R y),marginCode (P y))),
        tableOutput (paperListedEquiv r c hr hc x (listedPaddedDraw r c hr hc b h hb x completion))) := by
  unfold stepTranslation stepOldMargins stepNewMargins stepCompletion
  rw [stepCandidate_encoded r c e b h x y proposal completion hp]
  dsimp only [encodedStepInput]
  rw [residualParameters_code, residualParameters_code,listedPaddedDraw_code]

theorem profileStep_encoded (htotal : (∑ i,r i)=∑ j,c j)
    (x : PaperStates r c) (proposal : Fin s → Bool) (completion : Fin f → Bool) :
    profileStep (encodedStepInput r c e b h x proposal completion)=
      stateCode r c e (completionDecision R P x (decodedCodeProposal r c e x proposal)
        (paperListedEquiv r c hr hc x (listedPaddedDraw r c hr hc b h hb x completion))) := by
  have hp := codeProposal_encoded r c e htotal x proposal
  cases hd : decodedCodeProposal r c e x proposal with
  | none =>
    rw [hd,Option.map_none] at hp
    unfold profileStep
    have hcand : stepCandidateViews (encodedStepInput r c e b h x proposal completion)=stateCode r c e x := by
      simp only [stepCandidateViews,stepProposal,encodedStepInput,hp,Option.getD_none]
      rfl
    rw [hcand]
    split_ifs <;> rfl
  | some y =>
    rw [hd,Option.map_some] at hp
    have ht := stepTranslation_encoded r c e hr hc b h hb x y proposal completion hp
    have hv := translationValid_code (R x) (R y) (P x) (P y)
      (paperListedEquiv r c hr hc x (listedPaddedDraw r c hr hc b h hb x completion))
    unfold profileStep
    rw [ht]
    have hcand : stepCandidateViews (encodedStepInput r c e b h x proposal completion)=stateCode r c e y := by
      simp only [stepCandidateViews,stepProposal,encodedStepInput,hp,Option.getD_some]
    rw [hcand]
    rw [completionDecision_some_formula]
    exact apply_decision (stateCode r c e) x y _ _ hv


end
end ContingencyTables.SmallGraphProfiles

end OAI
