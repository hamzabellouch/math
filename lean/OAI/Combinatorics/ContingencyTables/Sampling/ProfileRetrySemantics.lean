import OAI.Combinatorics.ContingencyTables.Sampling.ProfileRetryProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTrialSemantics

namespace OAI

/-! # The executable retry program realizes the proved outer distribution -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres CompletionCounts
open FirstSuccess FairBits SmallContextCoordinates FirstPaperPhysicalMarginal
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

theorem profileRetry_code (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c)
    (steps attempts : ℕ) (fallback : Table r c)
    (bits : Fin (attempts*(steps*(s+f)+f)) → Bool) :
    profileRetry (((encodedConfiguration r c e h x x,((steps,s),f)),matrixCode fallback.val),
      List.ofFn bits)=
      matrixCode (listedOuterDraw r c e hr hc b h hb x steps attempts fallback bits).val := by
  have hf : 0<f := by positivity
  have hwidth : 0<steps*(s+f)+f := by omega
  unfold profileRetry profileRetryWords
  dsimp only [profileTrialWidth]
  rw [wordChunks_ofFn hwidth,FirstSuccessProgram.retry_ofFn]
  have he : (fun word : Fin (steps*(s+f)+f) → Bool =>
      packedProfileTrial ((encodedConfiguration r c e h x x,((steps,s),f)),List.ofFn word))=
      (fun word => (stateTrial r c (listedJointDraw r c e hr hc b h hb x steps word)).map
        (fun T => matrixCode T.val)) := by
    funext word
    exact packedProfileTrial_code r c e hr hc b h hb htotal x steps word
  rw [he,FirstSuccessProgram.wordRetry_map]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
