import OAI.Combinatorics.ContingencyTables.Sampling.UnitTrialProgram
import OAI.Combinatorics.ContingencyTables.Sampling.UnitOutputSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.UnitFiniteLaw

namespace OAI

/-! # All-small executable trials realize the uniform finite-word law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms FirstPaperPhysicalMarginal CompletionCounts
open FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] unitProfileRetry unitCodeOuterDraw
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma smallProposalBits_pos : 0<s := by
  apply Nat.clog_pos (by decide)
  have hd : 1≤dimensionAllowance (I := Fin m) (J := Fin n) := by unfold dimensionAllowance; omega
  have hs := Nat.pow_le_pow_left hd 2
  omega

lemma unitPackedTrial_ofFn (hsmall : ∀ i j,paperSmall r c i j=true)
    (htotal : (∑ i,r i)=∑ j,c j) (h : ℕ) (x : PaperStates r c)
    (steps f : ℕ) (bits : Fin (steps*s) → Bool) :
    unitPackedTrial ((encodedConfiguration r c e h x x,((steps,s),f)),List.ofFn bits)=
      (stateTrial r c (unitCodeJointDraw r c e (allSmallFibre r c hsmall) x steps bits)).map
        (fun T => matrixCode T.val) := by
  unfold unitPackedTrial unitPackedState unitPackedWords
  rw [wordChunks_ofFn (smallProposalBits_pos (m := m) (n := n))]
  rw [unitProfileWalk_ofFn r c e htotal,currentParameters_encoded]
  exact unitOuterTrial r c e hsmall _

lemma unitProfileRetry_code (hsmall : ∀ i j,paperSmall r c i j=true)
    (htotal : (∑ i,r i)=∑ j,c j) (h : ℕ) (x : PaperStates r c)
    (steps attempts f : ℕ) (hsteps : 0<steps) (fallback : Table r c)
    (bits : Fin (attempts*(steps*s)) → Bool) :
    unitProfileRetry (((encodedConfiguration r c e h x x,((steps,s),f)),matrixCode fallback.val),
      List.ofFn bits)=
      matrixCode (unitCodeOuterDraw r c e (allSmallFibre r c hsmall) x steps attempts fallback bits).val := by
  have hwidth : 0<steps*s := Nat.mul_pos hsteps (smallProposalBits_pos (m := m) (n := n))
  unfold unitProfileRetry unitRetryWords
  dsimp only [unitRetryWidth]
  rw [wordChunks_ofFn hwidth,FirstSuccessProgram.retry_ofFn]
  have he : (fun word : Fin (steps*s) → Bool =>
      unitPackedTrial ((encodedConfiguration r c e h x x,((steps,s),f)),List.ofFn word))=
      (fun word => (stateTrial r c (unitCodeJointDraw r c e (allSmallFibre r c hsmall) x steps word)).map
        (fun T => matrixCode T.val)) := by
    funext word
    exact unitPackedTrial_ofFn r c e hsmall htotal h x steps f word
  rw [he,FirstSuccessProgram.wordRetry_map]
  unfold unitCodeOuterDraw
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
