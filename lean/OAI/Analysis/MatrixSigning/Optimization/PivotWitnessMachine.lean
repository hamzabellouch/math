import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RationalElimination
import OAI.Analysis.MatrixSigning.Arithmetic.CleanRationalCompare
import OAI.Analysis.MatrixSigning.Matrices.PivotHistoryMachine
import OAI.Analysis.MatrixSigning.Optimization.StoredWitnessLift

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def witnessPorts : Fin 30 ↪ Fin 35 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,31,20,21,26,29,24,25,22,27,28,23],
    by decide⟩
def liftWitnessProgram : Program 35 := liftPorts KS.W12.StoredWitnessLift.program witnessPorts

def parentState {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (y : Fin n → ℚ) :
    Fin 35 → List Bool :=
  state saved (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M) []
    (KS.W12.RowDot.vectorTape y)

def liftedTape {n : ℕ} (M : DenseRatMatrix (n+1)) (y : Fin n → ℚ) : List Bool :=
  KS.W12.RowDot.vectorTape (schurWitnessLift (DenseRatMatrix.decode M) y)

theorem schurHead_eq {n : ℕ} (M : DenseRatMatrix (n+1)) (y : Fin n → ℚ) :
    Fin.cons (KS.W12.RowDot.schurHead M y) y = schurWitnessLift (DenseRatMatrix.decode M) y := by
  simp [KS.W12.RowDot.schurHead, schurWitnessLift, neg_div]

theorem liftWitness_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1))
    (y : Fin n → ℚ) :
    RunSpec liftWitnessProgram (parentState saved M y)
      (Function.update (parentState saved M y) 17 (liftedTape M y))
      (KS.W12.StoredWitnessLift.ticks M y) := by
  have h := KS.W12.StoredWitnessLift.full_spec M y
  rw [schurHead_eq] at h
  apply KS.W01.FixedPortRunSpec.lift_runSpec
    KS.W12.StoredWitnessLift.program witnessPorts (KS.W12.StoredWitnessLift.saved M y)
    (Function.update (KS.W12.StoredWitnessLift.saved M y) 17 (liftedTape M y)) _ _ _ h
  · intro i; fin_cases i <;> simp [parentState, state, witnessPorts, KS.W12.StoredWitnessLift.saved]
  · intro i; fin_cases i <;> simp [parentState, state, witnessPorts, KS.W12.StoredWitnessLift.saved,
      Function.update]
  · intro j hj
    have hj17 : j ≠ 17 := by simpa [witnessPorts] using hj 17
    simp [Function.update, hj17]

def witnessCleanup : Program 35 := KS.W04.CleanRationalCompare.clearListProgram 17 [26,31,23]
def replayProgram : Program 35 := compose (compose liftWitnessProgram witnessCleanup)
  (KS.W07.WireAppend.program 17 23 33)

def replayTicks {n : ℕ} (M : DenseRatMatrix (n+1)) (y : Fin n → ℚ) : ℕ :=
  KS.W12.StoredWitnessLift.ticks M y + KS.W12.StoredWitnessLift.inputLength M y +
    2 * (liftedTape M y).length + 6

theorem replay_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1))
    (y : Fin n → ℚ) :
    RunSpec replayProgram (parentState saved M y)
      (state saved [] [] [] (liftedTape M y)) (replayTicks M y) := by
  let b := Function.update (parentState saved M y) 17 (liftedTape M y)
  let c := Function.update (state saved [] [] [] []) 17 (liftedTape M y)
  have h1 := liftWitness_spec saved M y
  have h2 := KS.W04.CleanRationalCompare.clearList_spec (17 : Fin 35) [26,31,23] b
  have he : KS.W04.CleanRationalCompare.clearListState [26,31,23] b = c := by
    funext j; fin_cases j <;>
      simp [KS.W04.CleanRationalCompare.clearListState_apply, b, c, parentState, state, Function.update]
  have ht : KS.W04.CleanRationalCompare.clearListTicks [26,31,23] b =
      KS.W12.StoredWitnessLift.inputLength M y + 4 := by
    simp [KS.W04.CleanRationalCompare.clearListTicks, KS.W04.CleanRationalCompare.clearState,
      b, parentState, state, KS.W12.StoredWitnessLift.inputLength]
    omega
  rw [he, ht] at h2
  have h3 := KS.W07.WireAppend.spec (17 : Fin 35) 23 33 (by decide) (by decide) (by decide) c rfl
  have he3 : KS.W07.WireAppend.after 17 23 c = state saved [] [] [] (liftedTape M y) := by
    funext j; fin_cases j <;> simp [KS.W07.WireAppend.after, c, state]
  rw [he3] at h3
  have h := (h1.compose h2).compose h3
  convert h using 1 <;> simp [replayProgram, replayTicks, witnessCleanup, c]
  omega

def popReplayProgram : Program 35 := compose restoreProgram replayProgram

theorem popReplay_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1))
    (y : Fin n → ℚ) :
    RunSpec popReplayProgram
      (state (savedFrame (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M) ++ saved)
        [] [] [] (KS.W12.RowDot.vectorTape y))
      (state saved [] [] [] (liftedTape M y))
      ((9 * (Computability.encodeNat (n+1)).length + 3 * (KS.W08.denseMatrixTape M).length + 7) +
        replayTicks M y) :=
  (restore_spec saved (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M)
    (KS.W12.RowDot.vectorTape y)).compose (replay_spec saved M y)

end KS.W17.FixedPSD

end

end OAI
