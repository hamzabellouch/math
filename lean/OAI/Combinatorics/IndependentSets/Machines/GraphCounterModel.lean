import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineCopy
import OAI.Combinatorics.IndependentSets.Machines.MachineDrain
import OAI.Combinatorics.IndependentSets.Machines.MachineLogCounter

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.GraphCounterModel

open Turing

inductive ExtraTape where
  | input | archive | scratch | output
  deriving DecidableEq

instance : Fintype ExtraTape where
  elems := {.input, .archive, .scratch, .output}
  complete tape := by cases tape <;> simp

inductive ExtraLabel where
  | copyFirst | copySecond | seed | headerFirst | headerSecond
  | clearInput | clockCopy | archiveCopy | finalReverse
  deriving DecidableEq

instance : Fintype ExtraLabel where
  elems := {.copyFirst, .copySecond, .seed, .headerFirst, .headerSecond,
    .clearInput, .clockCopy, .archiveCopy, .finalReverse}
  complete label := by cases label <;> simp

abbrev Tape := Fin 3 ⊕ ExtraTape
abbrev Label := Fin 5 ⊕ ExtraLabel
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineLogCounter.State × Option Bool

def initialState : State := (MachineLogCounter.initialState, none)

def clockLabel : Option (Fin 5) → Option Label
  | none => some (.inr .clearInput)
  | some l => some (.inl l)

def clockStatement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State →
    TM2.Stmt Alphabet Label State
  | .push k f next => .push (.inl k) (fun state => f state.1) (clockStatement next)
  | .peek k f next => .peek (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .pop k f next => .pop (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (clockStatement next)
  | .branch f yes no => .branch (fun state => f state.1) (clockStatement yes) (clockStatement no)
  | .goto f => .goto (fun state => .inl (f state.1))
  | .halt => .goto (fun _ => .inr .clearInput)

def readHeader (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop (.inr .input) (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push (.inl 0) (fun _ => true) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def program : Label → TM2.Stmt Alphabet Label State
  | .inl l => clockStatement (MachineLogCounter.program l)
  | .inr .copyFirst => Reduction.MachineTransfer.loopAt (.inr .input) (.inr .scratch)
      id false (.inr .copyFirst) (some (.inr .copySecond))
  | .inr .copySecond => MachineCopy.forkLoop (.inr .scratch) (.inr .input) (.inr .archive)
      false (.inr .copySecond) (some (.inr .seed))
  | .inr .seed => .push (.inl 0) (fun _ => false) (.goto fun _ => .inr .headerFirst)
  | .inr .headerFirst => readHeader (.inr .headerFirst) (.inr .headerSecond)
  | .inr .headerSecond => readHeader (.inr .headerSecond) (.inl 0)
  | .inr .clearInput => MachineDrain.drain (.inr .input) (.inr .clearInput)
      (some (.inr .clockCopy))
  | .inr .clockCopy => Reduction.MachineTransfer.loopAt (.inl 2) (.inr .scratch)
      id false (.inr .clockCopy) (some (.inr .archiveCopy))
  | .inr .archiveCopy => Reduction.MachineTransfer.loopAt (.inr .archive) (.inr .scratch)
      id false (.inr .archiveCopy) (some (.inr .finalReverse))
  | .inr .finalReverse => Reduction.MachineTransfer.loopAt (.inr .scratch) (.inr .output)
      id false (.inr .finalReverse) none

def machine : FinTM2 where
  K := Tape
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := Alphabet
  Λ := Label
  main := .inr .copyFirst
  σ := State
  initialState := initialState
  m := program

def clockTapes (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool) : Tape → List Bool
  | .inl k => tapes k
  | .inr k => extra k

def clockConfiguration (extra : ExtraTape → List Bool) (register : Option Bool)
    (c : TM2.Cfg MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State) :
    TM2.Cfg Alphabet Label State := ⟨clockLabel c.l, (c.var, register), clockTapes c.stk extra⟩

theorem clockTapes_update (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool)
    (k : Fin 3) (word : List Bool) :
    clockTapes (Function.update tapes k word) extra =
      Function.update (clockTapes tapes extra) (.inl k) word := by
  funext tape
  cases tape <;> simp [clockTapes, Function.comp_def]

theorem clockStatement_simulation (extra : ExtraTape → List Bool) (register : Option Bool)
    (statement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State)
    (state : MachineLogCounter.State) (tapes : Fin 3 → List Bool) :
    TM2.stepAux (clockStatement statement) (state, register) (clockTapes tapes extra) =
      clockConfiguration extra register (TM2.stepAux statement state tapes) := by
  induction statement generalizing state tapes with
  | push k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [clockStatement, TM2.stepAux, clockTapes] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [clockStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

theorem clockStep (extra : ExtraTape → List Bool) (register : Option Bool)
    (a b : MachineLogCounter.machine.Cfg)
    (h : MachineLogCounter.machine.step a = some b) :
    TM2.step program (clockConfiguration extra register a) =
      some (clockConfiguration extra register b) := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => cases h
      | some label =>
          have hb := Option.some.inj h
          subst b
          exact congrArg some (clockStatement_simulation extra register
            (MachineLogCounter.program label) state tapes)

def clockInTime (extra : ExtraTape → List Bool) (register : Option Bool) (n : Nat) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration extra register (initList MachineLogCounter.machine (encodeWord n)))
      (some (clockConfiguration extra register
        (haltList MachineLogCounter.machine (encodeWord (n.log2 + 1))))) (8 * n + 4) :=
  MachineComposition.liftExecutionInTime _ _ (clockConfiguration extra register)
    (clockStep extra register) (MachineLogCounter.outputsInTime n)

end IndependentSetsGames.Foundations.Complexity.GraphCounterModel

end OAI
