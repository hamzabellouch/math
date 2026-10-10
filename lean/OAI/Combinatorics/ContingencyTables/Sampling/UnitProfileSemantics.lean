import OAI.Combinatorics.ContingencyTables.Sampling.UnitProfileProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTrialSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.AllSmallBoolean

namespace OAI

/-! # Exact finite-word semantics of the all-small profile walk -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] stateCode unitNext capViews codeNeighborProposal
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

def unitCodeBitStep (x : PaperStates r c) (bits : Fin s → Bool) : PaperStates r c :=
  (decodedCodeProposal r c e x bits).getD x

lemma unitNext_encoded (htotal : (∑ i,r i)=∑ j,c j) (h : ℕ)
    (initial x : PaperStates r c) (bits : Fin s → Bool) :
    unitNext (encodedConfiguration r c e h initial x,List.ofFn bits)=
      stateCode r c e (unitCodeBitStep r c e x bits) := by
  have hp := codeProposal_encoded r c e htotal x bits
  simp only [unitNext,unitCandidateInput,currentParameters_encoded,stepCandidateViews,stepProposal]
  change capViews (stateCodeData r c e initial,
    (codeNeighborProposal (stateCodeData r c e x,List.ofFn bits)).getD (stateCode r c e x))=_
  rw [hp]
  cases he : decodedCodeProposal r c e x bits with
  | none =>
    simp only [Option.map_none,Option.getD_none,unitCodeBitStep,he]
    exact capViews_stateCode r c e initial x
  | some y =>
    simp only [Option.map_some,Option.getD_some,unitCodeBitStep,he]
    exact capViews_stateCode r c e initial y

lemma unitAdvance_encoded (htotal : (∑ i,r i)=∑ j,c j) (h : ℕ)
    (initial x : PaperStates r c) (bits : Fin s → Bool) :
    unitAdvance (List.ofFn bits,encodedConfiguration r c e h initial x)=
      encodedConfiguration r c e h initial (unitCodeBitStep r c e x bits) := by
  apply Prod.ext
  · rfl
  ·
    have hn := unitNext_encoded r c e htotal h initial x bits
    simpa only [unitAdvance,encodedConfiguration] using hn

lemma unitProfileWalk_ofFn (htotal : (∑ i,r i)=∑ j,c j) (h : ℕ)
    (initial x : PaperStates r c) (steps : ℕ) (bits : Fin steps → Fin s → Bool) :
    unitProfileWalk (encodedConfiguration r c e h initial x,List.ofFn (fun i => List.ofFn (bits i)))=
      encodedConfiguration r c e h initial (wordWalk (unitCodeBitStep r c e) x steps bits) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    unfold unitProfileWalk at ih ⊢
    rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    change unitAdvance (List.ofFn (bits (Fin.last steps)),
      (List.ofFn (fun i => List.ofFn ((Fin.init bits) i))).foldl
        (fun state word => unitAdvance (word,state))
        (encodedConfiguration r c e h initial x))=_
    rw [ih (Fin.init bits)]
    exact unitAdvance_encoded r c e htotal h initial _ _

end
end ContingencyTables.SmallGraphProfiles

end OAI
