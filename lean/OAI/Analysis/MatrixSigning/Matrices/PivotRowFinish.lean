import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotRowInitialize

namespace OAI

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def foundFinish : Program 32 := compose
  (compose (KS.W04.BinaryStackMoves.clearProgram 25) (WireAppend.program 28 30 16))
  (WireAppend.program 24 29 16)
def emptyFinish : Program 32 := KS.W04.CleanRationalCompare.clearListProgram 29 [25,28,24]
def finishSelect (heads : Fin 32 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 32 :=
  ⟨if (heads 24).val = 0 then .right else .left, Vector.ofFn (fun _ => .stay)⟩
def finish : Program 32 := KS.W29.FixedBranch.branch foundFinish emptyFinish 29 finishSelect

def finished {n : ℕ} (M : DenseRatMatrix (n+1)) (idx : ℕ) (found : Bool) : Fin 32 → List Bool :=
  fun j => if j=31 then KS.W08.denseMatrixTape M else if j=26 then Computability.encodeNat (n+1) else
    if j=30 then if found then Computability.encodeNat idx else [] else
    if j=29 then if found then [true] else [] else []

def finishTicks (idx k : ℕ) : ℕ := 2*(Computability.encodeNat idx).length+k+10

theorem foundFinish_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (idx k : ℕ) :
    RunSpec foundFinish (state M idx k true) (finished M idx true)
      (k+1+(2*(Computability.encodeNat idx).length+2)+4) := by
  have h1 := KS.W04.CleanRationalCompare.clear_spec (25 : Fin 32) (state M idx k true)
  have he1 : KS.W04.CleanRationalCompare.clearState 25 (state M idx k true) = state M idx 0 true := by
    funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearState,state]
  rw [he1] at h1
  have h2 := WireAppend.spec (28 : Fin 32) 30 16 (by decide) (by decide) (by decide)
    (state M idx 0 true) rfl
  let t := WireAppend.after 28 30 (state M idx 0 true)
  have h3 := WireAppend.spec (24 : Fin 32) 29 16 (by decide) (by decide) (by decide) t rfl
  have he3 : WireAppend.after 24 29 t = finished M idx true := by
    funext j; fin_cases j <;> simp [WireAppend.after,t,state,finished]
  rw [he3] at h3
  have h := (h1.compose h2).compose h3
  convert h using 1 <;> simp [foundFinish,state,t,WireAppend.after]

theorem emptyFinish_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (idx k : ℕ) :
    RunSpec emptyFinish (state M idx k false) (finished M idx false)
      (k+(Computability.encodeNat idx).length+4) := by
  have h := KS.W04.CleanRationalCompare.clearList_spec (29 : Fin 32) [25,28,24] (state M idx k false)
  convert h using 1 <;> (try rfl)
  · funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearListState_apply,state,finished]
  · simp [KS.W04.CleanRationalCompare.clearListTicks,KS.W04.CleanRationalCompare.clearState,state]
    omega

theorem finish_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (idx k : ℕ) (found : Bool) :
    RunSpec finish (state M idx k found) (finished M idx found) (finishTicks idx k) := by
  cases found
  · have hs : ∀ coin, finishSelect (observedHeads
        (⟨some (KS.W29.FixedBranch.start foundFinish emptyFinish),state M idx k false⟩ :
          Config 32 (foundFinish.states+emptyFinish.states+1))) coin =
        ⟨.right,KS.W06.RationalCompare.stayActions 32⟩ := by
      intro coin; simp [finishSelect,state,observedHeads,KS.W29.topCode,KS.W06.RationalCompare.stayActions]
    apply (KS.W06.RationalCompare.branch_spec_right foundFinish emptyFinish 29 finishSelect _ _ _ hs
      (emptyFinish_spec M idx k)).mono
    unfold finishTicks
    omega
  · have hs : ∀ coin, finishSelect (observedHeads
        (⟨some (KS.W29.FixedBranch.start foundFinish emptyFinish),state M idx k true⟩ :
          Config 32 (foundFinish.states+emptyFinish.states+1))) coin =
        ⟨.left,KS.W06.RationalCompare.stayActions 32⟩ := by
      intro coin; simp [finishSelect,state,observedHeads,KS.W29.topCode,KS.W06.RationalCompare.stayActions]
    apply (KS.W06.RationalCompare.branch_spec_left foundFinish emptyFinish 29 finishSelect _ _ _ hs
      (foundFinish_spec M idx k)).mono
    unfold finishTicks
    omega

def completeProgram : Program 32 := compose offDiagonalProgram finish

theorem complete_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec completeProgram (initial M)
      (finished M (outcome M 1 n).index (outcome M 1 n).found)
      (initializeTicks n+ticks M b 1 n+finishTicks (outcome M 1 n).index (outcome M 1 n).remaining) :=
  (offDiagonal_spec M b hnum hden).compose
    (finish_spec M (outcome M 1 n).index (outcome M 1 n).remaining (outcome M 1 n).found)

end KS.W17.PivotRowLoop

end OAI
