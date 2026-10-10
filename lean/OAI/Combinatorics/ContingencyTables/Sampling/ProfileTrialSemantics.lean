import OAI.Combinatorics.ContingencyTables.Sampling.ProfileWordProgram
import OAI.Combinatorics.ContingencyTables.Transport.ListedOutputSemantics
import OAI.Combinatorics.ContingencyTables.Transport.BoundedProfileSemantics
import OAI.Combinatorics.ContingencyTables.Transport.ListedBooleanDraw

namespace OAI

/-! # The polynomial outer trial implements the finite-word experiment -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open FirstSuccess FairBits CompletionCounts SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

lemma currentParameters_encoded (initial x : PaperStates r c) :
    currentParameters (encodedConfiguration r c e h initial x)=
      ((stateCodeData r c e x,d^12),(d,h)) := rfl

theorem profileTrial_ofFn (htotal : (∑ i,r i)=∑ j,c j)
    (initial x : PaperStates r c) (steps : ℕ)
    (bits : Fin steps → Fin (s+f) → Bool) (terminal : Fin f → Bool) :
    profileTrial ((encodedConfiguration r c e h initial x,
      List.ofFn (fun i => (List.ofFn (splitWordEquiv s f (bits i)).1,
        List.ofFn (splitWordEquiv s f (bits i)).2))),List.ofFn terminal)=
      (stateTrial r c ⟨wordWalk (listedBitStep r c e hr hc b h hb) x steps bits,
        listedPaddedDraw r c hr hc b h hb _ terminal⟩).map (fun T => matrixCode T.val) := by
  unfold profileTrial trialOutputInput ProfilePrograms.trialCompletion trialParameters trialState
  rw [profileWalk_ofFn r c e hr hc b h hb htotal,currentParameters_encoded]
  rw [listedPaddedDraw_code r c hr hc e b h hb]
  exact actualOuterTrial r c e hr hc _ _

theorem packedProfileTrial_code (htotal : (∑ i,r i)=∑ j,c j)
    (x : PaperStates r c) (steps : ℕ) (bits : Fin (steps*(s+f)+f) → Bool) :
    packedProfileTrial ((encodedConfiguration r c e h x x,((steps,s),f)),List.ofFn bits)=
      (stateTrial r c (listedJointDraw r c e hr hc b h hb x steps bits)).map
        (fun T => matrixCode T.val) := by
  have hf : 0<f := by positivity
  unfold packedProfileTrial prepareProfileTrial profileTrialWords
  rw [profileWalkWords_ofFn (by omega),profileTerminalWord_ofFn]
  exact profileTrial_ofFn r c e hr hc b h hb htotal x x steps _ _

end
end ContingencyTables.SmallGraphProfiles

end OAI
