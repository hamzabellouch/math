import OAI.Computability.DepthThree.TapeParameterSearch
import OAI.Computability.DepthThree.TapeDivideFive
import Mathlib.Tactic.FinCases

namespace OAI

namespace DepthThreeLowerBound
namespace TapeParameters

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

def cubeRegisters : TapePowerSearch.Registers where
  toFun i := if i = 0 then 7 else if i = 1 then 3 else if i = 2 then 9
    else if i = 3 then 5 else 6
  inj' := by intro i j; fin_cases i <;> fin_cases j <;> decide

def sixthRegisters : TapePowerSearch.Registers where
  toFun i := if i = 0 then 7 else if i = 1 then 4 else if i = 2 then 9
    else if i = 3 then 5 else 2
  inj' := by intro i j; fin_cases i <;> fin_cases j <;> decide

@[simp] theorem cubeRegisters_zero : cubeRegisters 0 = 7 := rfl
@[simp] theorem cubeRegisters_one : cubeRegisters 1 = 3 := rfl
@[simp] theorem cubeRegisters_two : cubeRegisters 2 = 9 := rfl
@[simp] theorem cubeRegisters_three : cubeRegisters 3 = 5 := rfl
@[simp] theorem cubeRegisters_four : cubeRegisters 4 = 6 := rfl
@[simp] theorem sixthRegisters_zero : sixthRegisters 0 = 7 := rfl
@[simp] theorem sixthRegisters_one : sixthRegisters 1 = 4 := rfl
@[simp] theorem sixthRegisters_two : sixthRegisters 2 = 9 := rfl
@[simp] theorem sixthRegisters_three : sixthRegisters 3 = 5 := rfl
@[simp] theorem sixthRegisters_four : sixthRegisters 4 = 2 := rfl

def dataStore (σ : TapeStore) (n : ℕ) : TapeStore :=
  Function.update σ 2 (List.replicate (dataDimension n) true)

def outputStore (σ : TapeStore) (n : ℕ) : TapeStore :=
  Function.update
    (Function.update (dataStore σ n) 3 (List.replicate (hashDimension (dataDimension n)) true))
    4 (List.replicate (independenceOrder (dataDimension n)) true)

@[simp] theorem outputStore_data (σ : TapeStore) (n : ℕ) :
    outputStore σ n 2 = List.replicate (dataDimension n) true := by
  simp [outputStore, dataStore]

@[simp] theorem outputStore_hash (σ : TapeStore) (n : ℕ) :
    outputStore σ n 3 = List.replicate (hashDimension (dataDimension n)) true := by
  simp [outputStore]

@[simp] theorem outputStore_order (σ : TapeStore) (n : ℕ) :
    outputStore σ n 4 = List.replicate (independenceOrder (dataDimension n)) true := by
  simp [outputStore]

theorem outputStore_other (σ : TapeStore) (n : ℕ) (r : TapeRegister)
    (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) : outputStore σ n r = σ r := by
  simp [outputStore, dataStore, Function.update, h2, h3, h4]

abbrev LengthState := TapeCopy.State ⊕ TapeDivideFive.State

def lengthProgram : TapeMultiProgram LengthState :=
  joinCode (TapeCopy.code 1 5) (TapeDivideFive.program 5 2)
    (fun _ => TapeDivideFive.State.dec 0 .start)

def lengthStart : LengthState := .inl .start
def lengthDone (n : ℕ) : LengthState := .inr (.done (TapeDivideFive.residue n))

theorem runs_length (σ : TapeStore) (n : ℕ)
    (h1 : σ 1 = List.replicate n true) (h2 : σ 2 = []) (h5 : σ 5 = []) :
    RunsIn lengthProgram.step (cfg lengthStart (storeTapes σ))
      (cfg (lengthDone n) (storeTapes (dataStore σ n))) (10 * n + 8) := by
  let copied := Function.update σ 5 (List.replicate n true)
  have hcopy := TapeStoreRuns.copy (src := 1) (dst := 5) (by decide) σ h5
  simp only [h1, List.length_replicate] at hcopy
  have hi : onPair 5 2 (storeTapes copied) (counterTape n) (counterTape 0) =
      storeTapes copied :=
    TapeProductTerm.onPair_eq_self (by simp [copied, storeTapes, counterTape])
      (by simp [copied, storeTapes, counterTape, h2])
  have hrestore : Function.update copied 5 [] = σ := by
    dsimp [copied]
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.mpr h5.symm
  have ho : onPair 5 2 (storeTapes copied) (counterTape 0) (counterTape (n / 5)) =
      storeTapes (dataStore σ n) := by
    have he : onPair 5 2 (storeTapes copied) (counterTape 0) (counterTape (n / 5)) =
        storeTapes (Function.update (Function.update copied 5 []) 2
          (List.replicate (n / 5) true)) := by
      rw [onPair_eq_updates (by decide : (5 : TapeRegister) ≠ 2)]
      simp only [storeTapes_update, counterTape, List.replicate_zero]
    simpa only [hrestore, dataStore, dataDimension] using he
  have hdivide := TapeDivideFive.runs_divide (counter := 5) (destination := 2)
    (by decide) (storeTapes copied) n 0
  simp only [Nat.zero_add, hi, ho] at hdivide
  have h := join_runs (TapeCopy.code 1 5) (TapeDivideFive.program 5 2)
    (fun _ => TapeDivideFive.State.dec 0 .start) hcopy rfl hdivide
  have hc : 2 * n + 4 + 1 + (8 * n + 3) = 10 * n + 8 := by omega
  simpa only [lengthProgram, lengthStart, lengthDone, copied, hc] using h

abbrev SquareState := IncState ⊕ TapePower.State 2

def squareProgram : TapeMultiProgram SquareState :=
  joinCode (incProgram 6) (TapePower.program 2 6 2 7 5) (fun _ => TapePower.start 2)

def squareStart : SquareState := .inl .start
def squareDone : SquareState := .inr (TapePower.done 2)
def squareCost (d : ℕ) : ℕ := 2 + 1 + TapePower.cost 2 1 d

theorem runs_square (σ : TapeStore) (d : ℕ)
    (h2 : σ 2 = List.replicate d true) (h5 : σ 5 = [])
    (h6 : σ 6 = []) (h7 : σ 7 = []) :
    RunsIn squareProgram.step (cfg squareStart (storeTapes σ))
      (cfg squareDone (storeTapes (Function.update σ 6 (List.replicate (d ^ 2) true))))
      (squareCost d) := by
  have hinc := increment 6 (storeTapes σ) 0 (by simp [storeTapes, counterTape, h6])
  have hinner : onPair 7 5 (storeTapes σ) (counterTape 0) (counterTape 0) =
      storeTapes σ := TapeProductTerm.onPair_eq_self
        (by simp [storeTapes, counterTape, h7]) (by simp [storeTapes, counterTape, h5])
  have houter : onPair 6 2 (storeTapes σ) (counterTape 0) (counterTape d) =
      storeTapes σ := TapeProductTerm.onPair_eq_self
        (by simp [storeTapes, counterTape, h6]) (by simp [storeTapes, counterTape, h2])
  have hi : TapeMultiply.tapes 6 2 7 5 (storeTapes σ) 1 d 0 0 =
      Function.update (storeTapes σ) 6 (counterTape 1) := by
    unfold TapeMultiply.tapes
    rw [hinner]
    simpa only [houter] using
      (TapeArithmetic.update_onPair_src 6 2 (storeTapes σ)
        (counterTape 0) (counterTape d) (counterTape 1)).symm
  have hp := TapePower.runs_power 2 (outer := 6) (source := 2) (scratch := 7)
    (destination := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (storeTapes σ) 1 d
  have ho := TapePowerCompare.result_store 2 (outer := 6) (source := 2) (scratch := 7)
    (destination := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) σ d h6 h2 h7 h5
  change TapePower.resultTapes 2 6 2 7 5 (storeTapes σ) 1 d =
    storeTapes (Function.update σ 6 (List.replicate (d ^ 2) true)) at ho
  rw [hi, ho] at hp
  exact join_runs _ _ _ hinc rfl hp

abbrev FinishState := TapeErase.State ⊕ TapeParameterSearch.SixthState

def finishProgram : TapeMultiProgram FinishState :=
  joinCode (TapeErase.code 6) (TapeParameterSearch.sixthProgram sixthRegisters)
    (fun _ => TapeParameterSearch.sixthStart)

def finishStart : FinishState := .inl .start
def finishDone : FinishState := .inr TapeParameterSearch.sixthDone

abbrev RootsState := TapeParameterSearch.CubeState ⊕ FinishState

def rootsProgram : TapeMultiProgram RootsState :=
  joinCode (TapeParameterSearch.cubeProgram cubeRegisters) finishProgram (fun _ => finishStart)

def rootsStart : RootsState := .inl TapeParameterSearch.cubeStart
def rootsDone : RootsState := .inr finishDone

abbrev WorkState := SquareState ⊕ RootsState

def workProgram : TapeMultiProgram WorkState :=
  joinCode squareProgram rootsProgram (fun _ => rootsStart)

def workStart : WorkState := .inl squareStart
def workDone : WorkState := .inr rootsDone

abbrev State := LengthState ⊕ WorkState

def program : TapeMultiProgram State :=
  joinCode lengthProgram workProgram (fun _ => workStart)

def start : State := .inl lengthStart
def done : State := .inr workDone

def cost (n : ℕ) : ℕ :=
  10 * n + 2 * (dataDimension n) ^ 2 + 20 + TapePower.cost 2 1 (dataDimension n) +
    TapeParameterSearch.cubeCost (dataDimension n) +
    TapeParameterSearch.sixthCost (dataDimension n)

private theorem candidate_zero (R : TapePowerSearch.Registers) (σ : TapeStore)
    (h : σ (R 1) = []) : TapePowerSearch.candidateStore R σ 0 = σ := by
  change Function.update σ (R 1) [] = σ
  exact Function.update_eq_self_iff.mpr h.symm

theorem runs_parameters (σ : TapeStore) (n : ℕ)
    (h1 : σ 1 = List.replicate n true)
    (h2 : σ 2 = []) (h3 : σ 3 = []) (h4 : σ 4 = [])
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h7 : σ 7 = []) (h9 : σ 9 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (outputStore σ n))) (cost n) := by
  let d := dataDimension n
  let σD := dataStore σ n
  let σS := Function.update σD 6 (List.replicate (d ^ 2) true)
  let σC := Function.update σS 3 (List.replicate (hashDimension d) true)
  let σR := Function.update σD 3 (List.replicate (hashDimension d) true)
  have hlength := runs_length σ n h1 h2 h5
  have hsquare := runs_square σD d (by simp [σD, dataStore, d])
    (by simpa [σD, dataStore] using h5) (by simpa [σD, dataStore] using h6)
    (by simpa [σD, dataStore] using h7)
  have hcube := TapeParameterSearch.runs_cube cubeRegisters σS d
    (by simpa [σS, σD, dataStore] using h7)
    (by simpa [σS, σD, dataStore] using h9)
    (by simpa [σS, σD, dataStore] using h5)
    (by simp [σS])
  have hc0 : TapePowerSearch.candidateStore cubeRegisters σS 0 = σS :=
    candidate_zero cubeRegisters σS (by simpa [σS, σD, dataStore] using h3)
  rw [hc0] at hcube
  change RunsIn (TapeParameterSearch.cubeProgram cubeRegisters).step
    (cfg TapeParameterSearch.cubeStart (storeTapes σS))
    (cfg TapeParameterSearch.cubeDone (storeTapes σC))
    (TapeParameterSearch.cubeCost d) at hcube
  have herase := TapeStoreRuns.erase 6 σC
  have hclear : Function.update σC 6 [] = σR := by
    funext r
    by_cases hr : r = 6
    · subst r
      simp [σR, σD, dataStore, h6]
    · simp [σC, σR, σS, Function.update, hr]
  have hc6 : σC 6 = List.replicate (d ^ 2) true := by simp [σC, σS]
  rw [hclear, hc6, List.length_replicate] at herase
  have hsixth := TapeParameterSearch.runs_sixth sixthRegisters σR d
    (by simpa [σR, σD, dataStore] using h7)
    (by simpa [σR, σD, dataStore] using h9)
    (by simpa [σR, σD, dataStore] using h5)
    (by simp [σR, σD, dataStore, d])
  have hs0 : TapePowerSearch.candidateStore sixthRegisters σR 0 = σR :=
    candidate_zero sixthRegisters σR (by simpa [σR, σD, dataStore] using h4)
  rw [hs0] at hsixth
  change RunsIn (TapeParameterSearch.sixthProgram sixthRegisters).step
    (cfg TapeParameterSearch.sixthStart (storeTapes σR))
    (cfg TapeParameterSearch.sixthDone (storeTapes (outputStore σ n)))
    (TapeParameterSearch.sixthCost d) at hsixth
  have hfinish := join_runs (TapeErase.code 6) (TapeParameterSearch.sixthProgram sixthRegisters)
    (fun _ => TapeParameterSearch.sixthStart) herase rfl hsixth
  have hroots := join_runs (TapeParameterSearch.cubeProgram cubeRegisters) finishProgram
    (fun _ => finishStart) hcube rfl hfinish
  have hwork := join_runs squareProgram rootsProgram (fun _ => rootsStart) hsquare rfl hroots
  have h := join_runs lengthProgram workProgram (fun _ => workStart) hlength rfl hwork
  apply h.mono
  dsimp only [cost, squareCost, d]
  omega

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeParameters
end DepthThreeLowerBound

end OAI
