import OAI.Computability.DepthThree.TapeInitialization
import OAI.Computability.DepthThree.TapeParametersBound
import OAI.Computability.DepthThree.TapeInputGuard

namespace OAI

namespace DepthThreeLowerBound
namespace TapeParse

open TapeMultiProgram TapeRouting

def inputStore (w : List Bool) : TapeStore := fun r =>
  if r = TapeRegister.input then w
  else if r = TapeRegister.length then List.replicate w.length true else []

theorem initializedTapes_eq_store (w : List Bool) :
    initializedTapes w = storeTapes (inputStore w) := by
  funext r
  unfold initializedTapes storeTapes inputStore
  split_ifs <;> rfl

def outputStore (w : List Bool) : TapeStore :=
  TapeInputGuard.outputStore (TapeParameters.outputStore (inputStore w) w.length)
    (dataDimension w.length) (hashDimension (dataDimension w.length))
    (independenceOrder (dataDimension w.length))

@[simp] theorem outputStore_input (w : List Bool) : outputStore w 0 = w := by
  simp [outputStore, TapeInputGuard.outputStore, TapeParameters.outputStore,
    TapeParameters.dataStore, inputStore, TapeRegister.input]

@[simp] theorem outputStore_data (w : List Bool) :
    outputStore w 2 = List.replicate (dataDimension w.length) true := by
  simp [outputStore, TapeInputGuard.outputStore]

@[simp] theorem outputStore_hash (w : List Bool) :
    outputStore w 3 = List.replicate (hashDimension (dataDimension w.length)) true := by
  simp [outputStore, TapeInputGuard.outputStore]

@[simp] theorem outputStore_order (w : List Bool) :
    outputStore w 4 = List.replicate (independenceOrder (dataDimension w.length)) true := by
  simp [outputStore, TapeInputGuard.outputStore]

theorem outputStore_empty (w : List Bool) (r : TapeRegister)
    (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3)
    (h4 : r ≠ 4) (h8 : r ≠ 8) : outputStore w r = [] := by
  simp [outputStore, TapeInputGuard.outputStore, TapeParameters.outputStore,
    TapeParameters.dataStore, inputStore, TapeRegister.input, TapeRegister.length,
    Function.update, h0, h1, h2, h3, h4, h8]

abbrev WorkState := TapeParameters.State ⊕ TapeInputGuard.State

def workProgram : TapeMultiProgram WorkState :=
  joinCode TapeParameters.program TapeInputGuard.program (fun _ => TapeInputGuard.start)

def workStart : WorkState := .inl TapeParameters.start
def workDone (accepted : Bool) : WorkState := .inr (TapeInputGuard.done accepted)

abbrev State := InitState ⊕ WorkState

def program : TapeMultiProgram State :=
  joinCode initializationCode workProgram (fun _ => workStart)

def start : State := .inl InitState.start
def done (accepted : Bool) : State := .inr (workDone accepted)

def acceptFlag : State → Bool
  | .inr (.inr (.inr (.inr (.done b)))) => b
  | _ => false

@[simp] theorem acceptFlag_done (b : Bool) : acceptFlag (done b) = b := rfl

@[simp] theorem program_done (b : Bool) (h : TapeHeads) : program (done b) h = none := rfl

theorem runs_parse (w : List Bool) :
    RunsIn program.step (cfg start (rawInputTapes w))
      (cfg (done (decide (InputFits w))) (storeTapes (outputStore w)))
      (1000 * (w.length + 3) ^ 8) := by
  let σ := inputStore w
  let τ := TapeParameters.outputStore σ w.length
  have hi := initialization_runs w
  rw [initializedTapes_eq_store] at hi
  have hp := TapeParameters.runs_parameters σ w.length
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
  have hp' := hp.mono (TapeParameters.cost_le w.length)
  have hg := TapeInputGuard.runs_inputFits_quadratic w τ
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [τ]) (by simp [τ]) (by simp [τ])
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
  have hw := join_runs TapeParameters.program TapeInputGuard.program
    (fun _ => TapeInputGuard.start) hp' (by simp) hg
  have hall := join_runs initializationCode workProgram (fun _ => workStart) hi rfl hw
  apply hall.mono
  have hquad : (w.length + 1) ^ 2 ≤ (w.length + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : w.length + 1 ≤ w.length + 3) 2)
      (Nat.pow_le_pow_right (by omega : 0 < w.length + 3) (by decide : 2 ≤ 8))
  have hn : w.length ≤ (w.length + 3) ^ 8 := by
    calc
      w.length ≤ w.length + 3 := by omega
      _ = (w.length + 3) ^ 1 := by simp
      _ ≤ (w.length + 3) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 1 ≤ (w.length + 3) ^ 8 := Nat.pow_pos (by omega)
  omega

end TapeParse
end DepthThreeLowerBound

end OAI
