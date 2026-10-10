import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Computation.MachineCanonicalOutput
import OAI.Computability.BinPacking.Computation.MachineRegularExecutionBounds
import OAI.Computability.BinPacking.Computation.MachineRegularVertexBlock
import OAI.Computability.BinPacking.PCP.PreprocessingFamilyBridge

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition

namespace Lift

open MachineCloudPadding

variable {K K' Λ Λ' σ τ υ : Type}

def statement (tape : K → K') (labels : Λ → Λ') (exit : Option Λ')
    (registers : (σ × τ) ≃ υ) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2.Stmt (fun _ : K' => Bool) Λ' υ :=
  MachineStateEquiv.statement registers
    (MachineStateFrame.frameStatement (Placement.statement tape labels exit q))

def configuration (view : K' → Option K) (labels : Λ → Λ') (exit : Option Λ')
    (registers : (σ × τ) ≃ υ) (ambient : τ) (extra : K' → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) : TM2.Cfg (fun _ : K' => Bool) Λ' υ :=
  ⟨Placement.label labels exit c.l, registers (c.var, ambient),
    Placement.tapes view c.stk extra⟩

variable [DecidableEq K] [DecidableEq K']

theorem stepAux (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (source : K → List Bool) :
    TM2.stepAux (statement tape labels exit registers q) (registers (state, ambient))
        (Placement.tapes view source extra) =
      configuration view labels exit registers ambient extra (TM2.stepAux q state source) := by
  rw [statement, MachineStateEquiv.stepAux_transport, MachineStateFrame.frame_stepAux,
    Placement.stepAux_simulation tape view left right]
  rfl

theorem step (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' υ)
    (code : ∀ l, target (labels l) = statement tape labels exit registers (source l))
    (a b : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration view labels exit registers ambient extra a) =
      some (configuration view labels exit registers ambient extra b) := by
  cases a with
  | mk label state sourceTapes =>
    cases label with
    | none => simp [TM2.step] at h
    | some label =>
      have hb : TM2.stepAux (source label) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      change some (TM2.stepAux (target (labels label)) (registers (state, ambient))
        (Placement.tapes view sourceTapes extra)) = _
      rw [code, stepAux tape view left right]

theorem trace (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' υ)
    (code : ∀ l, target (labels l) = statement tape labels exit registers (source l))
    (steps : Nat) (a b : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (run : (advance (TM2.step source))^[steps] (some a) = some b) :
    (advance (TM2.step target))^[steps]
      (some (configuration view labels exit registers ambient extra a)) =
      some (configuration view labels exit registers ambient extra b) :=
  liftSuccessfulTrace _ _ _
    (step tape view left right labels exit registers ambient extra source target code) steps a b run

end Lift

end BinPackingGames.Foundations.Complexity.MachineRegularTable

namespace BinPackingGames.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition
open MachineCloudPadding

abbrev CoreTape := Fin 27
abbrev NativeTape := MachinePaddedExpanderFamily.Tape
abbrev Tape := CoreTape ⊕ NativeTape
abbrev Alphabet (_ : Tape) := Bool
abbrev SmallTable := MachinePaddedExpanderFamily.SmallTable
abbrev FamilyState := MachineExpanderFamily.State Unit MachinePaddedExpanderFamily.fixedDegree
abbrev State := (FamilyState × Bool) × Option Bool

def inputNative : NativeTape := .inr .input
def outputNative : NativeTape := .inl MachineExpanderFamily.tableTape
def powerNative : NativeTape := .inr .power
def sizeNative : NativeTape := .inl (.inr .currentSize)
def levelNative : NativeTape := .inl (.inr .remainingLevel)

def powerTape : Tape := .inr powerNative
def sizeTape : Tape := .inr sizeNative
def levelTape : Tape := .inr levelNative

def familyTape (t : NativeTape) : Tape :=
  if t = inputNative then .inl 4 else if t = outputNative then .inl 7 else .inr t

def familyView : Tape → Option NativeTape
  | .inl i => if i = 4 then some inputNative else if i = 7 then some outputNative else none
  | .inr t => if t = inputNative then none else if t = outputNative then none else some t

theorem familyView_left (t : NativeTape) : familyView (familyTape t) = some t := by
  by_cases hi : t = inputNative
  · subst t; simp [familyTape, familyView]
  · by_cases ho : t = outputNative
    · subst t; simp [familyTape, familyView, hi]
    · simp [familyTape, familyView, hi, ho]

theorem familyView_right (j : Tape) (t : NativeTape)
    (h : familyView j = some t) : familyTape t = j := by
  cases j with
  | inl i =>
    by_cases hi : i = 4
    · subst i
      have ht : inputNative = t := by simpa [familyView] using h
      subst t; simp [familyTape]
    · by_cases ho : i = 7
      · subst i
        have ht : outputNative = t := by simpa [familyView] using h
        subst t; simp [familyTape, inputNative, outputNative]
      · simp [familyView, hi, ho] at h
  | inr j =>
    by_cases hi : j = inputNative
    · simp [familyView, hi] at h
    · by_cases ho : j = outputNative
      · simp [familyView, ho] at h
      · have ht : j = t := by simpa [familyView, hi, ho] using h
        subst t; simp [familyTape, hi, ho]

def stateEquiv : MachinePaddedExpanderFamily.State Unit ≃ State :=
  (Equiv.prodAssoc FamilyState Bool (Option Bool)).symm

def seedState (H : SmallTable) : FamilyState :=
  MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()

def readyState (H : SmallTable) : State := ((seedState H, false), none)

def sourceProgram (H : SmallTable) : MachinePaddedExpanderFamily.Label →
    TM2.Stmt (fun _ : NativeTape => Bool) MachinePaddedExpanderFamily.Label State :=
  MachineStateEquiv.program stateEquiv (MachinePaddedExpanderFamily.program (ρ := Unit) H)

inductive Label
  | start
  | family (label : MachinePaddedExpanderFamily.Label)
  | drainPower | drainSize | drainLevel
  deriving DecidableEq, Fintype

def program (H : SmallTable) : Label → TM2.Stmt Alphabet Label State
  | .start => .load (fun _ => readyState H) (.goto fun _ => .family MachinePaddedExpanderFamily.main)
  | .family l => Placement.statement familyTape Label.family (some .drainPower) (sourceProgram H l)
  | .drainPower => MachineDrain.drain powerTape .drainPower (some .drainSize)
  | .drainSize => MachineDrain.drain sizeTape .drainSize (some .drainLevel)
  | .drainLevel => MachineDrain.drain levelTape .drainLevel none

def frame (core : CoreTape → List Bool) : Tape → List Bool
  | .inl i => core i
  | .inr _ => []

def rotor (H : SmallTable) (k : Nat) : List Bool :=
  MachinePaddedExpanderFamilyBounds.outputWord H k

def resultCore (H : SmallTable) (k : Nat) (core : CoreTape → List Bool) :
    CoreTape → List Bool := Function.update core 7 (rotor H k)

def working (core : CoreTape → List Bool) (power size level : List Bool) : Tape → List Bool
  | .inl i => core i
  | .inr t => if t = powerNative then power
      else if t = sizeNative then size else if t = levelNative then level else []

@[simp] theorem working_power (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l powerTape = p := by simp [working, powerTape]

@[simp] theorem working_size (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l sizeTape = s := by
  simp [working, sizeTape, powerNative, sizeNative]

@[simp] theorem working_level (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l levelTape = l := by
  simp [working, levelTape, powerNative, sizeNative, levelNative]

theorem update_working_power (core : CoreTape → List Bool) (p s l p' : List Bool) :
    Function.update (working core p s l) powerTape p' = working core p' s l := by
  funext t
  cases t with
  | inl i => simp [working, powerTape]
  | inr t => by_cases h : t = powerNative <;> simp [working, powerTape, h]

theorem update_working_size (core : CoreTape → List Bool) (p s l s' : List Bool) :
    Function.update (working core p s l) sizeTape s' = working core p s' l := by
  funext t
  cases t with
  | inl i => simp [working, sizeTape]
  | inr t =>
    by_cases h : t = sizeNative
    · subst t; simp [working, sizeTape, powerNative, sizeNative]
    · simp [working, sizeTape, h]

theorem update_working_level (core : CoreTape → List Bool) (p s l l' : List Bool) :
    Function.update (working core p s l) levelTape l' = working core p s l' := by
  funext t
  cases t with
  | inl i => simp [working, levelTape]
  | inr t =>
    by_cases h : t = levelNative
    · subst t; simp [working, levelTape, powerNative, sizeNative, levelNative]
    · simp [working, levelTape, h]

@[simp] theorem working_empty (core : CoreTape → List Bool) :
    working core [] [] [] = frame core := by
  funext t; cases t <;> simp [working, frame]

private theorem initial_other (k : Nat) (t : NativeTape) (h : t ≠ inputNative) :
    MachinePaddedExpanderFamily.initialTapes k t = [] := by
  cases t with
  | inl t => rfl
  | inr t => cases t <;> simp_all [MachinePaddedExpanderFamily.initialTapes, inputNative]

private theorem final_other (H : SmallTable) (k : Nat) (t : NativeTape)
    (hi : t ≠ inputNative) (ho : t ≠ outputNative) (hp : t ≠ powerNative)
    (hs : t ≠ sizeNative) (hl : t ≠ levelNative) :
    MachinePaddedExpanderFamily.finalTapes H k t = [] := by
  rcases t with ((row | tableExtra) | familyExtra) | ceiling
  · cases row <;>
      simp_all [inputNative, outputNative, MachineExpanderFamily.tableTape,
        MachinePaddedExpanderFamily.finalTapes, MachineExpanderFamily.toBoolTapes,
        MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
        MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.tableFrame,
        MachineEmbedding.tapes]
  · cases tableExtra <;> rfl
  · cases familyExtra <;>
      simp_all [sizeNative, levelNative, MachinePaddedExpanderFamily.finalTapes,
        MachineExpanderFamily.toBoolTapes, MachineExpanderFamily.toBoolWord,
        MachineExpanderFamily.familyTapes, MachineExpanderFamily.boundaryTapes,
        MachineExpanderFamily.extraFrame, MachineEmbedding.tapes]
  · cases ceiling <;>
      simp_all [inputNative, powerNative, MachinePaddedExpanderFamily.finalTapes,
        MachinePaddedExpanderFamily.retainedCeilingTapes, MachineCeilingPower.memory]

theorem initial_placement (k : Nat) (core : CoreTape → List Bool)
    (hinput : core 4 = encodeWord k) (houtput : core 7 = []) :
    Placement.tapes familyView (MachinePaddedExpanderFamily.initialTapes k) (frame core) =
      frame core := by
  funext t
  cases t with
  | inl i =>
    by_cases hi : i = 4
    · subst i; simp [Placement.tapes, familyView, frame, inputNative, hinput]
    · by_cases ho : i = 7
      · subst i
        simp [Placement.tapes, familyView, frame, outputNative,
          MachinePaddedExpanderFamily.initialTapes, houtput]
      · simp [Placement.tapes, familyView, frame, hi, ho]
  | inr t =>
    by_cases hi : t = inputNative
    · simp [Placement.tapes, familyView, frame, hi]
    · by_cases ho : t = outputNative
      · simp [Placement.tapes, familyView, frame, ho]
      · simp [Placement.tapes, familyView, frame, hi, ho, initial_other k t hi]

theorem final_placement (H : SmallTable) (k : Nat) (core : CoreTape → List Bool)
    (hinput : core 4 = encodeWord k) :
    Placement.tapes familyView (MachinePaddedExpanderFamily.finalTapes H k) (frame core) =
      working (resultCore H k core)
        (encodeWord (PCP.PreprocessingLevels.paddedSize k))
        (encodeWord (PCP.PreprocessingLevels.paddedSize k)) (encodeWord 0) := by
  funext t
  cases t with
  | inl i =>
    by_cases hi : i = 4
    · subst i
      simp [Placement.tapes, familyView, working, resultCore, inputNative, hinput]
    · by_cases ho : i = 7
      · subst i
        simp [Placement.tapes, familyView, working, resultCore, outputNative,
          rotor, MachinePaddedExpanderFamilyBounds.outputWord]
        change MachinePaddedExpanderFamily.finalTapes H k
          (MachinePaddedExpanderFamily.familyTape MachineExpanderFamily.tableTape) = _
        exact MachinePaddedExpanderFamily.finalTapes_table H k
      · simp [Placement.tapes, familyView, working, resultCore, frame, hi, ho]
  | inr t =>
    by_cases hi : t = inputNative
    · subst t
      simp [Placement.tapes, familyView, working, frame,
        inputNative, powerNative, sizeNative, levelNative]
    · by_cases ho : t = outputNative
      · subst t
        simp [Placement.tapes, familyView, working, frame,
          outputNative, MachineExpanderFamily.tableTape, inputNative,
          powerNative, sizeNative, levelNative]
      · by_cases hp : t = powerNative
        · subst t
          simp [Placement.tapes, familyView, working, powerNative, inputNative, outputNative]
        · by_cases hs : t = sizeNative
          · subst t
            simpa [Placement.tapes, familyView, working, sizeNative,
              powerNative, inputNative, outputNative, MachineExpanderFamily.tableTape,
              MachinePaddedExpanderFamily.familyTape] using
              MachinePaddedExpanderFamily.finalTapes_currentSize H k
          · by_cases hl : t = levelNative
            · subst t
              simpa [Placement.tapes, familyView, working, levelNative,
                sizeNative, powerNative, inputNative, outputNative,
                MachineExpanderFamily.tableTape, MachinePaddedExpanderFamily.ceilingTape] using
                MachinePaddedExpanderFamily.finalTapes_remainingLevel H k
            · simp [Placement.tapes, familyView, working, hi, ho, hp, hs, hl,
                final_other H k t hi ho hp hs hl]

@[simp] theorem source_initial_state (H : SmallTable) :
    stateEquiv (MachinePaddedExpanderFamily.initialState (seedState H) none) =
      readyState H := rfl

@[simp] theorem source_final_state (H : SmallTable) :
    stateEquiv (MachinePaddedExpanderFamily.finalState H (seedState H)) =
      readyState H := by
  simp [stateEquiv, MachinePaddedExpanderFamily.finalState, readyState, seedState]

noncomputable def familyInTime (H : SmallTable) (k : Nat) (core : CoreTape → List Bool)
    (hinput : core 4 = encodeWord k) (houtput : core 7 = []) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some (.family MachinePaddedExpanderFamily.main), readyState H, frame core⟩
      (some ⟨some .drainPower, readyState H,
        working (resultCore H k core)
          (encodeWord (PCP.PreprocessingLevels.paddedSize k))
          (encodeWord (PCP.PreprocessingLevels.paddedSize k)) (encodeWord 0)⟩)
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord k).length) := by
  let raw := MachinePaddedExpanderFamily.paddedInTime H k (seedState H) none
  let renamed := MachineStateEquiv.execution stateEquiv
    (MachinePaddedExpanderFamily.program (ρ := Unit) H) raw
  let placed := liftExecutionInTime (TM2.step (sourceProgram H)) (TM2.step (program H))
    (Placement.configuration familyView Label.family (some .drainPower) (frame core))
    (Placement.step_simulation familyTape familyView familyView_left familyView_right
      Label.family (some .drainPower) (frame core) (sourceProgram H) (program H)
      (fun _ => rfl)) renamed
  simpa only [MachineStateEquiv.configuration, Placement.configuration, Placement.label,
    source_initial_state, source_final_state, initial_placement k core hinput houtput,
    final_placement H k core hinput] using placed

private theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

theorem cleanupTrace (H : SmallTable) (m : Nat) (core : CoreTape → List Bool) :
    (advance (TM2.step (program H)))^[2*m+6]
      (some ⟨some .drainPower, readyState H,
        working core (encodeWord m) (encodeWord m) (encodeWord 0)⟩) =
      some ⟨none, readyState H, frame core⟩ := by
  have first := (MachineDrain.drainInTime powerTape .drainPower (some .drainSize)
    (program H) rfl (working core (encodeWord m) (encodeWord m) (encodeWord 0))
    (seedState H, false) none).evals_in_steps
  have second := (MachineDrain.drainInTime sizeTape .drainSize (some .drainLevel)
    (program H) rfl (working core [] (encodeWord m) (encodeWord 0))
    (seedState H, false) none).evals_in_steps
  have third := (MachineDrain.drainInTime levelTape .drainLevel none
    (program H) rfl (working core [] [] (encodeWord 0))
    (seedState H, false) none).evals_in_steps
  simp only [MachineDrain.drainInTime, working_power, working_size, working_level,
    encodeWord_length, update_working_power, update_working_size,
    update_working_level, working_empty] at first second third
  have all := appendTrace _ (appendTrace _ first second) third
  have count : 2*m+6 = (m+1+1)+(m+1+1)+(0+1+1) := by omega
  rw [count]
  exact all

def cleanupInTime (H : SmallTable) (m : Nat) (core : CoreTape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some .drainPower, readyState H,
        working core (encodeWord m) (encodeWord m) (encodeWord 0)⟩
      (some ⟨none, readyState H, frame core⟩) (2*m+6) where
  steps := 2*m+6
  evals_in_steps := cleanupTrace H m core
  steps_le_m := le_rfl

def startInTime (H : SmallTable) (core : CoreTape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some .start, state, frame core⟩
      (some ⟨some (.family MachinePaddedExpanderFamily.main), readyState H, frame core⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program H .start) state (frame core)) = _
    rfl
  steps_le_m := le_rfl

noncomputable def timePolynomial : Polynomial Nat :=
  MachinePaddedExpanderFamilyBounds.timePolynomial +
    Polynomial.C (2 * PCP.ExpanderFamily.growth) * Polynomial.X + 7

theorem totalBudget_le (k : Nat) :
    1 + MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord k).length +
        (2 * PCP.PreprocessingLevels.paddedSize k + 6) ≤
      timePolynomial.eval (encodeWord k).length := by
  have hs := MachineExpanderFamilyBounds.paddedSize_le_succ_input k
  have hm := Nat.mul_le_mul_left 2 hs
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, encodeWord_length]
  simp only [Nat.mul_assoc] at hm ⊢
  omega

noncomputable def familyCleanInTime (H : SmallTable) (k : Nat)
    (core : CoreTape → List Bool) (hinput : core 4 = encodeWord k)
    (houtput : core 7 = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some .start, state, frame core⟩
      (some ⟨none, readyState H, frame (resultCore H k core)⟩)
      (timePolynomial.eval (encodeWord k).length) := by
  let first := startInTime H core state
  let second := familyInTime H k core hinput houtput
  let third := cleanupInTime H (PCP.PreprocessingLevels.paddedSize k) (resultCore H k core)
  let pair := StateTransition.EvalsToInTime.trans (TM2.step (program H)) _ _ _ _ _ first second
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H)) _ _ _ _ _ pair third
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
  exact all.steps_le_m.trans
    (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using totalBudget_le k)

@[simp] theorem result_output (H : SmallTable) (k : Nat) (core : CoreTape → List Bool) :
    frame (resultCore H k core) (.inl 7) = rotor H k := by simp [frame, resultCore]

theorem result_preserves_core (H : SmallTable) (k : Nat) (core : CoreTape → List Bool)
    (i : CoreTape) (hi : i ≠ 7) : frame (resultCore H k core) (.inl i) = core i := by
  simp [frame, resultCore, hi]

@[simp] theorem result_private_empty (H : SmallTable) (k : Nat)
    (core : CoreTape → List Bool) (t : NativeTape) :
    frame (resultCore H k core) (.inr t) = [] := rfl

noncomputable def placedInTime {K Λ : Type} [DecidableEq K]
    (tape : Tape → K) (view : K → Option Tape)
    (left : ∀ t, view (tape t) = some t)
    (right : ∀ j t, view j = some t → tape t = j)
    (labels : Label → Λ) (exit : Option Λ) (extra : K → List Bool)
    (H : SmallTable) (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ State)
    (code : ∀ l, target (labels l) = Placement.statement tape labels exit (program H l))
    (k : Nat) (core : CoreTape → List Bool) (hinput : core 4 = encodeWord k)
    (houtput : core 7 = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step target)
      (Placement.configuration view labels exit extra ⟨some .start, state, frame core⟩)
      (some (Placement.configuration view labels exit extra
        ⟨none, readyState H, frame (resultCore H k core)⟩))
      (timePolynomial.eval (encodeWord k).length) :=
  liftExecutionInTime (TM2.step (program H)) (TM2.step target)
    (Placement.configuration view labels exit extra)
    (Placement.step_simulation tape view left right labels exit extra (program H) target code)
    (familyCleanInTime H k core hinput houtput state)

end BinPackingGames.Foundations.Complexity.MachineRegularFamily

namespace BinPackingGames.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

abbrev Tape := Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕ MachinePaddedExpanderFamily.Tape)
abbrev Alphabet (_ : Tape) := Bool
abbrev CoreState := MachineRegularInternalRow.CoreState Unit internalDegree
abbrev MetaState := MachineRegularMetadata.State Unit
abbrev FamilyState := MachineRegularFamily.State
abbrev State := (CoreState × MetaState) × FamilyState
abbrev Data := MachineRegularMetadata.Data
abbrev BaseTable := PreprocessingRegularTables.BaseTable

theorem degree_positive : 0 < internalDegree :=
  Nat.mul_pos MachineExpanderFamily.baseDegree_positive MachineExpanderFamily.baseDegree_positive

def readyState (H : BaseTable) : State :=
  ((MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
    (((), false), none)), MachineRegularFamily.readyState H)

def metadataTape : MachineRegularMetadata.Tape → Tape
  | .inl i => .inl i
  | .inr e => .inr (.inl e)

def metadataView : Tape → Option MachineRegularMetadata.Tape
  | .inl i => some (.inl i)
  | .inr (.inl e) => some (.inr e)
  | .inr (.inr _) => none

def familyTape : MachineRegularFamily.Tape → Tape
  | .inl i => .inl i
  | .inr e => .inr (.inr e)

def familyView : Tape → Option MachineRegularFamily.Tape
  | .inl i => some (.inl i)
  | .inr (.inl _) => none
  | .inr (.inr e) => some (.inr e)

def vertexView : Tape → Option (Fin 27)
  | .inl i => some i
  | .inr _ => none

theorem metadataView_left (k : MachineRegularMetadata.Tape) :
    metadataView (metadataTape k) = some k := by cases k <;> rfl

theorem metadataView_right (j : Tape) (k : MachineRegularMetadata.Tape)
    (h : metadataView j = some k) : metadataTape k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr j => cases j with
    | inl e => cases h; rfl
    | inr e => cases h

theorem familyView_left (k : MachineRegularFamily.Tape) :
    familyView (familyTape k) = some k := by cases k <;> rfl

theorem familyView_right (j : Tape) (k : MachineRegularFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr j => cases j with
    | inl e => cases h
    | inr e => cases h; rfl

theorem vertexView_left (k : Fin 27) : vertexView (.inl k) = some k := rfl

theorem vertexView_right (j : Tape) (k : Fin 27)
    (h : vertexView j = some k) : Sum.inl k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr e => cases h

def metadataStates : (MetaState × (CoreState × FamilyState)) ≃ State where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def familyStates : (FamilyState × (CoreState × MetaState)) ≃ State := Equiv.prodComm _ _
def vertexStates : (CoreState × (MetaState × FamilyState)) ≃ State :=
  (Equiv.prodAssoc _ _ _).symm

inductive Label
  | metadata (l : MachineRegularMetadata.Label)
  | family (l : MachineRegularFamily.Label)
  | vertex (l : MachineRegularVertexBlock.Label internalDegree)
  | clear (i : Fin 7)
  deriving DecidableEq, Fintype

def entry : Label := .metadata (.owner .seed)

def clearTape : Fin 7 → Tape :=
  ![.inl 2, .inl 3, .inl 4, .inl 5, .inl 7,
    .inr (.inl .padding), .inr (.inl .level)]

def clearEntry (k : Nat) : Option Label :=
  if h : k < 7 then some (.clear ⟨k, h⟩) else none

def clearSource (source : Tape) : Unit → TM2.Stmt Alphabet Unit MetaState :=
  fun _ => MachineDrain.drain source () none

def vertexSource : MachineRegularVertexBlock.Label internalDegree →
    TM2.Stmt (fun _ : Fin 27 => Bool) (MachineRegularVertexBlock.Label internalDegree) CoreState :=
  MachineRegularVertexBlock.instruction internalDegree degree_positive id none

def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .metadata l => Lift.statement metadataTape Label.metadata (some (.family .start))
      metadataStates (MachineRegularMetadata.program l)
  | .family l => Lift.statement familyTape Label.family
      (some (.vertex (MachineRegularVertexBlock.originalEntry internalDegree degree_positive)))
      familyStates (MachineRegularFamily.program H l)
  | .vertex l => Lift.statement Sum.inl Label.vertex (clearEntry 0)
      vertexStates (vertexSource l)
  | .clear i => Lift.statement id (fun _ : Unit => .clear i) (clearEntry (i.val + 1))
      metadataStates (clearSource (clearTape i) ())

def frame (data : Data) : Tape → List Bool
  | .inl i => MachineRegularMetadata.frame data (.inl i)
  | .inr (.inl e) => MachineRegularMetadata.frame data (.inr e)
  | .inr (.inr _) => []

def coreFrame (data : Data) (i : Fin 27) : List Bool :=
  MachineRegularMetadata.frame data (.inl i)

def cfg (H : BaseTable) (label : Option Label) (data : Data) : TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data⟩

def initialData (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := encodeWord e.val
  owner := []
  localRank := []
  count := []
  offset := []
  darts := encodeWord t.darts
  rotor := []
  output := output
  padding := []
  level := []

def metadataData (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) : Data :=
  MachineRegularMetadata.originalData t e (initialData t e output)

def familyData (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Data :=
  { metadataData t e output with
    rotor := MachineRegularFamily.rotor H (cloudSize t t.rows[e].tail) }

def emittedBits (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  PreprocessingRegularWords.originalVertexBits t (padding t) (familyCloudTable H t) e

def emittedData (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Data :=
  { familyData H t e output with output := output ++ emittedBits H t e }

private theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem metadataPlacement (data extra : Data) :
    MachineCloudPadding.Placement.tapes metadataView (MachineRegularMetadata.frame data)
      (frame extra) = frame data := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j <;> rfl

theorem metadataTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularMetadata.totalTime t e]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H (some (.family .start)) (metadataData t e output)) := by
  have raw := MachineRegularMetadata.originalTrace t e (initialData t e output)
    rfl rfl rfl rfl rfl rfl rfl rfl () none
  have placed := Lift.trace metadataTape metadataView metadataView_left metadataView_right
    Label.metadata (some (.family .start)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) (frame (initialData t e output))
    MachineRegularMetadata.program (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    metadataPlacement, MachineRegularMetadata.cfg, metadataData, cfg, readyState,
    metadataStates, Equiv.coe_fn_mk, entry] using placed

theorem familyPlacement (data : Data) :
    MachineCloudPadding.Placement.tapes familyView (MachineRegularFamily.frame (coreFrame data))
      (frame data) = frame data := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j <;> rfl

theorem familyResultPlacement (H : BaseTable) (k : Nat) (data : Data) :
    MachineCloudPadding.Placement.tapes familyView
      (MachineRegularFamily.frame (MachineRegularFamily.resultCore H k (coreFrame data)))
      (frame data) = frame { data with rotor := MachineRegularFamily.rotor H k } := by
  funext j
  cases j with
  | inl i => fin_cases i <;>
      simp [MachineCloudPadding.Placement.tapes, familyView, MachineRegularFamily.frame,
        MachineRegularFamily.resultCore, coreFrame, frame, MachineRegularMetadata.frame]
  | inr j => cases j with
    | inl e => cases e <;> rfl
    | inr e => rfl

noncomputable def familyExecution (H : BaseTable) (t : GraphTables.Table)
    (e : Fin t.darts) (output : List Bool) :=
  MachineRegularFamily.familyCleanInTime H (cloudSize t t.rows[e].tail)
    (coreFrame (metadataData t e output)) rfl rfl (MachineRegularFamily.readyState H)

noncomputable def familySteps (H : BaseTable) (t : GraphTables.Table)
    (e : Fin t.darts) (output : List Bool) : Nat :=
  (familyExecution H t e output).steps

theorem familyTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[familySteps H t e output]
      (some (cfg H (some (.family .start)) (metadataData t e output))) =
      some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output)) := by
  have raw := (familyExecution H t e output).evals_in_steps
  have placed := Lift.trace familyTape familyView familyView_left familyView_right
    Label.family (some (.vertex (MachineRegularVertexBlock.originalEntry internalDegree degree_positive)))
    familyStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      ((((), false), none) : MetaState)) (frame (metadataData t e output))
    (MachineRegularFamily.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    familyPlacement, familyResultPlacement, familyData, familySteps, cfg, readyState,
    familyStates, Equiv.prodComm_apply, Prod.swap_prod_mk] using placed

def clearMemory (base : Tape → List Bool) : Nat → Tape → List Bool
  | 0 => base
  | k + 1 => if h : k < 7 then
      Function.update (clearMemory base k) (clearTape ⟨k, h⟩) [] else clearMemory base k

def clearSteps (base : Tape → List Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => clearSteps base k + if h : k < 7 then
      ((clearMemory base k) (clearTape ⟨k, h⟩)).length + 1 else 0

private theorem identityPlacement (base extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes some base extra = base := rfl

theorem drainTrace (H : BaseTable) (i : Fin 7) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[(base (clearTape i)).length + 1]
      (some ⟨some (.clear i), readyState H, base⟩) =
      some ⟨clearEntry (i.val + 1), readyState H, Function.update base (clearTape i) []⟩ := by
  have raw := MachineDrain.drainTrace (clearTape i) () none (clearSource (clearTape i)) rfl
    base (base (clearTape i)) ((), false) none
  simp only [Function.update_eq_self] at raw
  have placed := Lift.trace id some (fun _ => rfl)
    (fun j k h => (Option.some.inj h).symm)
    (fun _ : Unit => Label.clear i) (clearEntry (i.val + 1)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) base (clearSource (clearTape i)) (program H)
    (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    identityPlacement, metadataStates, Equiv.coe_fn_mk, readyState] using placed

theorem clearPrefixTrace (H : BaseTable) (base : Tape → List Bool)
    (k : Nat) (hk : k ≤ 7) :
    (advance (TM2.step (program H)))^[clearSteps base k]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨clearEntry k, readyState H, clearMemory base k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < 7 := by omega
    have first := ih (by omega)
    have second := drainTrace H ⟨k, h⟩ (clearMemory base k)
    have atEntry : clearEntry k = some (.clear ⟨k, h⟩) := by simp only [clearEntry, dite_eq_left h]
    rw [atEntry] at first
    simpa only [clearSteps, clearMemory, dite_eq_left h] using joinTrace first second

theorem clearTrace (H : BaseTable) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[clearSteps base 7]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨none, readyState H, clearMemory base 7⟩ := by
  simpa only [clearEntry, lt_self_iff_false, dite_false] using clearPrefixTrace H base 7 le_rfl

theorem clearFrame (data : Data) : clearMemory (frame data) 7 =
    frame { data with
      owner := []
      localRank := []
      count := []
      offset := []
      rotor := []
      padding := []
      level := [] } := by
  funext j
  cases j with
  | inl i => fin_cases i <;>
      simp [clearMemory, clearTape, frame, MachineRegularMetadata.frame]
  | inr j => cases j with
    | inl e => cases e <;>
        simp [clearMemory, clearTape, frame, MachineRegularMetadata.frame]
    | inr e => simp [clearMemory, clearTape, frame]

theorem coreFrame_eq (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    coreFrame (familyData H t e output) =
      MachineRegularInternalRow.coreInputTapes t (padding t) (familyCloudTable H t)
        t.rows[e].tail (MachineRegularVertexBlock.oldCloud t (padding t) e) output := by
  have rotor : MachineRegularFamily.rotor H (cloudSize t t.rows[e].tail) =
      encodeWords (ExpanderTableWords.rotationWords (familyCloudTable H t t.rows[e].tail)) :=
    PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t t.rows[e].tail
      (PreprocessingFamilyBridge.cloudSize_pos_of_dart t e)
  funext i
  fin_cases i <;>
    simp [coreFrame, familyData, metadataData, MachineRegularMetadata.originalData,
      MachineRegularMetadata.cloudData, MachineRegularMetadata.prefixData,
      MachineRegularMetadata.rankData, MachineRegularMetadata.ownerData,
      MachineRegularMetadata.frame, initialData,
      MachineRegularInternalRow.coreInputTapes, MachineRegularInternalRow.coreMemory,
      MachineRegularVertexBlock.oldCloud, paddedOld,
      MachineRegularMetadata.originalMember]
  all_goals first | exact rotor | rfl

theorem emittedData_eq (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : emittedData H t e output =
      familyData H t e (output ++ emittedBits H t e) := rfl

theorem vertexPlacement (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output output' : List Bool) :
    MachineCloudPadding.Placement.tapes vertexView (coreFrame (familyData H t e output'))
      (frame (familyData H t e output)) = frame (familyData H t e output') := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j with
    | inl e => cases e <;> rfl
    | inr e => rfl

def vertexSteps (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Nat :=
  MachineRegularVertexBlock.originalSteps t (padding t) (familyCloudTable H t) e output.length

theorem vertexTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[vertexSteps H t e output]
      (some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output))) =
      some (cfg H (clearEntry 0) (emittedData H t e output)) := by
  have raw := MachineRegularVertexBlock.originalTraceAt internalDegree degree_positive id none
    vertexSource (fun _ => rfl) t (padding t) (familyCloudTable H t) e output ()
  have finished := coreFrame_eq H t e (output ++ emittedBits H t e)
  simp only [emittedBits] at finished
  rw [← coreFrame_eq H t e output, ← finished] at raw
  have placed := Lift.trace Sum.inl vertexView vertexView_left vertexView_right
    Label.vertex (clearEntry 0) vertexStates
    (((((), false), none) : MetaState), MachineRegularFamily.readyState H)
    (frame (familyData H t e output)) vertexSource (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, vertexPlacement,
    emittedData_eq, cfg, readyState, vertexStates, Equiv.prodAssoc_symm_apply,
    vertexSteps, emittedBits, id_eq] using placed

noncomputable def totalSteps (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Nat :=
  MachineRegularMetadata.totalTime t e + familySteps H t e output + vertexSteps H t e output +
    clearSteps (frame (emittedData H t e output)) 7

theorem originalTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[totalSteps H t e output]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H none (initialData t e (output ++ emittedBits H t e))) := by
  have metadata := metadataTrace H t e output
  have family := familyTrace H t e output
  have vertex := vertexTrace H t e output
  have cleanup := clearTrace H (frame (emittedData H t e output))
  have final : clearMemory (frame (emittedData H t e output)) 7 =
      frame (initialData t e (output ++ emittedBits H t e)) := by
    rw [clearFrame]
    rfl
  rw [final] at cleanup
  exact joinTrace (joinTrace (joinTrace metadata family) vertex) cleanup

noncomputable def originalExecution (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (cfg H (some entry) (initialData t e output))
      (some (cfg H none (initialData t e (output ++ emittedBits H t e))))
      (totalSteps H t e output) where
  steps := totalSteps H t e output
  evals_in_steps := originalTrace H t e output
  steps_le_m := le_rfl

end BinPackingGames.Foundations.Complexity.MachineRegularOriginalBody

namespace BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2
abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev Alphabet (_ : Tape) := Bool

private def sumDecidableEq {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

instance tapeDecidableEq : DecidableEq Tape :=
  sumDecidableEq
    (sumDecidableEq (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq
          (sumDecidableEq
            (sumDecidableEq (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (inferInstanceAs (DecidableEq (Fin 2)))

instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕ Fin 2)
  infer_instance

def core (k : Fin 27) : Tape := .inl (.inl k)
def localRank : Tape := core 3
def count : Tape := core 4
def prefixTape : Tape := core 5
def rotor : Tape := core 7
def padding : Tape := .inl (.inr (.inl .padding))
def level : Tape := .inl (.inr (.inl .level))
def dummyFuel : Tape := .inr 0
def scratch : Tape := .inr 1

def cleanupTapes : List Tape := [localRank, count, rotor, padding, level, dummyFuel]

inductive Label
  | scan
  | restore
  | drain (l : MachineDrainMany.Label cleanupTapes)
  deriving DecidableEq, Fintype

def entry : Label := .scan

variable {Λ : Type}

def cleanupEntry (labels : Label → Λ) (exit : Option Λ) : Option Λ :=
  MachineDrainMany.entry cleanupTapes (fun l => labels (.drain l)) exit

def instruction (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ State
  | .scan => MachineUnaryAffineAt.scan padding scratch prefixTape 1
      (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch padding id false
      (labels .restore) (cleanupEntry labels exit)
  | .drain l => MachineDrainMany.instruction cleanupTapes
      (fun l => labels (.drain l)) exit l

def afterAddition (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  Function.update base prefixTape (encodeWord (d + o))

def finalTapes (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  MachineDrainMany.finalTapes cleanupTapes (afterAddition base d o)

def steps (base : Tape → List Bool) (d : Nat) : Nat :=
  2 * (d + 1) + (cleanupTapes.map (fun k => (base k).length + 1)).sum

theorem finalTapes_apply (base : Tape → List Bool) (d o : Nat) (k : Tape) :
    finalTapes base d o k =
      if k ∈ cleanupTapes then []
      else if k = prefixTape then encodeWord (d + o) else base k := by
  simp only [finalTapes, MachineDrainMany.finalTapes_apply, afterAddition,
    Function.update_apply]

@[simp] theorem finalTapes_prefix (base : Tape → List Bool) (d o : Nat) :
    finalTapes base d o prefixTape = encodeWord (d + o) := by
  simp [finalTapes_apply, cleanupTapes, prefixTape, localRank, count, rotor,
    padding, level, dummyFuel, core]

theorem finalTapes_empty (base : Tape → List Bool) (d o : Nat) (k : Tape)
    (hk : k ∈ cleanupTapes) : finalTapes base d o k = [] := by
  rw [finalTapes_apply, ite_eq_left hk]

theorem finalTapes_other (base : Tape → List Bool) (d o : Nat) (k : Tape)
    (hk : k ∉ cleanupTapes) (hp : k ≠ prefixTape) :
    finalTapes base d o k = base k := by
  rw [finalTapes_apply, ite_eq_right hk, ite_eq_right hp]

@[simp] theorem finalTapes_scratch (base : Tape → List Bool) (d o : Nat) :
    finalTapes base d o scratch = base scratch := by
  apply finalTapes_other
  · simp [cleanupTapes, scratch, localRank, count, rotor, padding, level, dummyFuel, core]
  · decide

theorem drainSteps_eq (base : Tape → List Bool) (d o : Nat) :
    MachineDrainMany.steps cleanupTapes (afterAddition base d o) =
      (cleanupTapes.map (fun k => (base k).length + 1)).sum := by
  simp [MachineDrainMany.steps, cleanupTapes, afterAddition, prefixTape,
    localRank, count, rotor, padding, level, dummyFuel, core]

theorem additionTraceAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (d + 1)]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨cleanupEntry labels exit, (ambient, none), afterAddition base d o⟩ := by
  have frame (word : List Bool) :
      MachineUnaryAffineAt.tapes padding scratch prefixTape base (encodeWord d) [] word =
        Function.update base prefixTape word := by
    rw [← paddingWord, ← scratchEmpty]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have initial : MachineUnaryAffineAt.tapes padding scratch prefixTape base
      (encodeWord d) [] (encodeWord o) = base := by
    rw [frame, ← prefixWord, Function.update_eq_self]
  have run := MachineUnaryAffineAt.affineTrace padding scratch prefixTape
    (by decide) (by decide) (by decide) 1 (labels .scan) (labels .restore)
    (cleanupEntry labels exit) program (code .scan) (code .restore)
    base d o [] [] ambient register
  simpa only [List.append_nil, Nat.one_mul, initial, frame, entry, afterAddition] using run

theorem traceAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[steps base d]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), finalTapes base d o⟩ := by
  have first := additionTraceAt labels exit program code base d o
    paddingWord prefixWord scratchEmpty ambient register
  have second := MachineDrainMany.trace cleanupTapes (fun l => labels (.drain l)) exit
    program (fun l => code (.drain l)) (afterAddition base d o) ambient none
  simp only [MachineDrainMany.finalRegister_none, drainSteps_eq] at second
  unfold steps
  rw [Nat.add_comm, Function.iterate_add_apply, first]
  exact second

def executionAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels entry), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), finalTapes base d o⟩) (steps base d) where
  steps := steps base d
  evals_in_steps := traceAt labels exit program code base d o
    paddingWord prefixWord scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

end BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup

namespace BinPackingGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds MachineRegularOriginalBody

noncomputable def wide : Polynomial Nat := Polynomial.C (ExpanderFamily.growth + 1) * Polynomial.X
noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  wide + wide * Polynomial.C (q + 1) + 8192
noncomputable def outputPolynomial (q : Nat) : Polynomial Nat :=
  wide + Polynomial.C q * rowPolynomial q
noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10*wide + 2*wide + 13*wide + 5*wide +
    Polynomial.C (5*q+10)*(wide+wide) + 4*wide + 2*outputPolynomial q +
      Polynomial.C (8*q+41066)
noncomputable def blockPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C q * corePolynomial q + Polynomial.C (5*q+20)*wide +
    2*outputPolynomial q + Polynomial.C (5*q+40995)
noncomputable def cleanupPolynomial (q : Nat) : Polynomial Nat := 6*wide + rotorPolynomial q + 13
noncomputable def timePolynomial : Polynomial Nat :=
  MachineRegularMetadata.timePolynomial + MachineRegularExecutionBounds.familyPolynomial +
    blockPolynomial internalDegree + cleanupPolynomial internalDegree

def bodySize (t : GraphTables.Table) (output : List Bool) : Nat :=
  inputLength t + output.length

theorem blockPolynomial_eval (q L : Nat) :
    (blockPolynomial q).eval L =
      MachineRegularVertexBlock.originalTimeBound q
        ((ExpanderFamily.growth+1)*L) ((rotorPolynomial q).eval L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L) := by
  simp only [blockPolynomial, corePolynomial, outputPolynomial, rowPolynomial, wide,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, MachineRegularVertexBlock.originalTimeBound,
    MachineRegularVertexBlock.portTimeBound, MachineRegularInternalRow.coreTimeBound,
    MachineRegularOriginalClean.timeBound, MachineRegularVertexBlock.rowSizeBound]
  ring

theorem originalTimeBound_le (q L R x v i k o m O V W R' : Nat)
    (hL : L ≤ W) (hR : R ≤ R') (hx : x ≤ W) (hv : v ≤ W)
    (hi : i ≤ W) (hk : k ≤ W) (ho : o ≤ W) (hm : m ≤ W)
    (hO : O ≤ W) (hV : V ≤ W) :
    MachineRegularVertexBlock.originalTimeBound q L R x v i k o m O V ≤
      MachineRegularVertexBlock.originalTimeBound q W R' W W W W W W W W := by
  unfold MachineRegularVertexBlock.originalTimeBound MachineRegularVertexBlock.portTimeBound
    MachineRegularInternalRow.coreTimeBound MachineRegularOriginalClean.timeBound
    MachineRegularVertexBlock.rowSizeBound
  gcongr

theorem wide_le (t : GraphTables.Table) (output : List Bool) :
    inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    ExpanderFamily.growth*inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    output.length ≤ (ExpanderFamily.growth+1)*bodySize t output := by
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hO : output.length ≤ bodySize t output := Nat.le_add_left _ _
  have hg := Nat.mul_le_mul_left ExpanderFamily.growth hN
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem vertexSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    MachineRegularOriginalBody.vertexSteps H t e output ≤
      (blockPolynomial internalDegree).eval (bodySize t output) := by
  let v := t.rows[e].tail
  let W := (ExpanderFamily.growth+1)*bodySize t output
  have bounds := wide_le t output
  have hx := e.isLt.le.trans (GraphTables.darts_le_tableBits_length t)
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hk := cloudSize_le_input t v
  have hi := (cloudRank t v (MachineRegularMetadata.originalMember t e)).isLt.le.trans hk
  have hm := GraphTables.darts_le_tableBits_length t
  have ho := prefix_le_input t v.val
  have hV := regularVertices_le_input t
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  have raw := MachineRegularVertexBlock.originalSteps_le internalDegree degree_positive
    t (padding t) (familyCloudTable H t) e output.length
  have bound := originalTimeBound_le internalDegree _ _ _ _ _ _ _ _ _ _ W _
    bounds.1 hR (hx.trans bounds.1) (hv.trans bounds.1) (hi.trans bounds.1)
    (hk.trans bounds.1) (ho.trans bounds.2.1) (hm.trans bounds.1) bounds.2.2
    (hV.trans bounds.2.1)
  rw [blockPolynomial_eval]
  exact raw.trans bound

theorem clearSteps_frame (data : Data) :
    clearSteps (frame data) 7 = data.owner.length + data.localRank.length +
      data.count.length + data.offset.length + data.rotor.length + data.padding.length +
      data.level.length + 7 := by
  simp [clearSteps, clearMemory, clearTape, frame, MachineRegularMetadata.frame]
  omega

theorem cleanupSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    clearSteps (frame (emittedData H t e output)) 7 ≤
      (cleanupPolynomial internalDegree).eval (bodySize t output) := by
  let v := t.rows[e].tail
  have bounds := wide_le t output
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hk := cloudSize_le_input t v
  have hi := (cloudRank t v (MachineRegularMetadata.originalMember t e)).isLt.le.trans hk
  have ho := prefix_le_input t v.val
  have hp := cloudTotal_le_input t v
  have hl := level_le_input t v
  have hrotor := PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v
    (PreprocessingFamilyBridge.cloudSize_pos_of_dart t e)
  change MachineRegularFamily.rotor H (cloudSize t v) = _ at hrotor
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  rw [← hrotor] at hR
  rw [clearSteps_frame]
  simp only [emittedData, familyData, metadataData, MachineRegularMetadata.originalData,
    MachineRegularMetadata.cloudData, MachineRegularMetadata.prefixData,
    MachineRegularMetadata.rankData, MachineRegularMetadata.ownerData, initialData,
    encodeWord_length, cleanupPolynomial, wide, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  change _ ≤ 6*((ExpanderFamily.growth+1)*bodySize t output) +
    (rotorPolynomial internalDegree).eval (bodySize t output)+13
  change cloudSize t v + MachineCloudPadding.padding (cloudSize t v) ≤ _ at hp
  dsimp only [v, bodySize, inputLength] at *
  omega

theorem totalSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    totalSteps H t e output ≤ timePolynomial.eval (bodySize t output) := by
  have hsize : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hm := (MachineRegularMetadata.totalTime_le t e).trans
    (natPolynomial_eval_mono MachineRegularMetadata.timePolynomial hsize)
  have hf := (familyExecution H t e output).steps_le_m
  have hfb := MachineRegularExecutionBounds.family_budget_le t t.rows[e].tail
  simp only [MachineRegularFamily.timePolynomial, encodeWord_length,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat] at hf
  have hf' := (hf.trans hfb).trans
    (natPolynomial_eval_mono MachineRegularExecutionBounds.familyPolynomial hsize)
  have hv := vertexSteps_le H t e output
  have hc := cleanupSteps_le H t e output
  simp only [totalSteps, familySteps, timePolynomial, Polynomial.eval_add]
  omega

noncomputable def originalInTime (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (cfg H (some entry) (initialData t e output))
      (some (cfg H none (initialData t e (output ++ emittedBits H t e))))
      (timePolynomial.eval (bodySize t output)) where
  steps := totalSteps H t e output
  evals_in_steps := originalTrace H t e output
  steps_le_m := totalSteps_le H t e output

end BinPackingGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

namespace BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev Data := MachineRegularMetadata.Data
abbrev CoreState := MachineRegularOriginalBody.CoreState
abbrev MetaState := MachineRegularOriginalBody.MetaState
abbrev FamilyState := MachineRegularOriginalBody.FamilyState
abbrev BaseTable := PreprocessingRegularTables.BaseTable

instance : DecidableEq Tape := MachineRegularOwnerCleanup.tapeDecidableEq
instance : Fintype Tape := MachineRegularOwnerCleanup.tapeFintype

def core (k : Fin 27) : Tape := .inl (.inl k)
def paddingTape : Tape := .inl (.inr (.inl .padding))
def levelTape : Tape := .inl (.inr (.inl .level))
def dummyFuel : Tape := .inr 0
def scratch : Tape := .inr 1

def readyState (H : BaseTable) : State := (MachineRegularOriginalBody.readyState H, none)

def metadataTape (k : MachineRegularMetadata.Tape) : Tape :=
  .inl (MachineRegularOriginalBody.metadataTape k)

def metadataView : Tape → Option MachineRegularMetadata.Tape
  | .inl k => MachineRegularOriginalBody.metadataView k
  | .inr _ => none

def familyTape (k : MachineRegularFamily.Tape) : Tape :=
  .inl (MachineRegularOriginalBody.familyTape k)

def familyView : Tape → Option MachineRegularFamily.Tape
  | .inl k => MachineRegularOriginalBody.familyView k
  | .inr _ => none

def vertexView : Tape → Option (Fin 27)
  | .inl k => MachineRegularOriginalBody.vertexView k
  | .inr _ => none

theorem metadataView_left (k : MachineRegularMetadata.Tape) :
    metadataView (metadataTape k) = some k := MachineRegularOriginalBody.metadataView_left k

theorem metadataView_right (j : Tape) (k : MachineRegularMetadata.Tape)
    (h : metadataView j = some k) : metadataTape k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.metadataView_right j k h)
  | inr j => cases h

theorem familyView_left (k : MachineRegularFamily.Tape) :
    familyView (familyTape k) = some k := MachineRegularOriginalBody.familyView_left k

theorem familyView_right (j : Tape) (k : MachineRegularFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.familyView_right j k h)
  | inr j => cases h

theorem vertexView_left (k : Fin 27) : vertexView (core k) = some k := rfl

theorem vertexView_right (j : Tape) (k : Fin 27)
    (h : vertexView j = some k) : core k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.vertexView_right j k h)
  | inr j => cases h

def metadataStates : (MetaState × ((CoreState × FamilyState) × Option Bool)) ≃ State where
  toFun p := (((p.2.1.1, p.1), p.2.1.2), p.2.2)
  invFun p := (p.1.1.2, ((p.1.1.1, p.1.2), p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def familyStates : (FamilyState × ((CoreState × MetaState) × Option Bool)) ≃ State where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def vertexStates : (CoreState × ((MetaState × FamilyState) × Option Bool)) ≃ State where
  toFun p := (((p.1, p.2.1.1), p.2.1.2), p.2.2)
  invFun p := (p.1.1.1, ((p.1.1.2, p.1.2), p.2))
  left_inv _ := rfl
  right_inv _ := rfl

inductive Label
  | metadata (l : MachineRegularMetadata.Label)
  | copyCount (l : MachineUnaryAffineAt.Label)
  | copyFuel (l : MachineUnaryAffineAt.Label)
  | guard
  | family (l : MachineRegularFamily.Label)
  | loop
  | vertex (l : MachineRegularVertexBlock.Label internalDegree)
  | bump
  | cleanup (l : MachineRegularOwnerCleanup.Label)
  deriving DecidableEq, Fintype

def entry : Label := .metadata (.cloud .init)

def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .metadata l => Lift.statement metadataTape Label.metadata (some (.copyCount .seed))
      metadataStates (MachineRegularMetadata.program l)
  | .copyCount .seed => MachineUnaryAffineAt.seed (core 3) 0 (.copyCount .scan)
  | .copyCount .scan => MachineUnaryAffineAt.scan (core 4) scratch (core 3) 1
      (.copyCount .scan) (.copyCount .restore)
  | .copyCount .restore => Reduction.MachineTransfer.loopAt scratch (core 4) id false
      (.copyCount .restore) (some (.copyFuel .seed))
  | .copyFuel .seed => MachineUnaryAffineAt.seed dummyFuel 0 (.copyFuel .scan)
  | .copyFuel .scan => MachineUnaryAffineAt.scan paddingTape scratch dummyFuel 1
      (.copyFuel .scan) (.copyFuel .restore)
  | .copyFuel .restore => Reduction.MachineTransfer.loopAt scratch paddingTape id false
      (.copyFuel .restore) (some .guard)
  | .guard => .peek dummyFuel (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .family .start))
        (.load (fun state => (state.1, none))
          (.goto fun _ => .cleanup MachineRegularOwnerCleanup.entry)))
  | .family l => Lift.statement familyTape Label.family (some .loop)
      familyStates (MachineRegularFamily.program H l)
  | .loop => .peek dummyFuel (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.pop dummyFuel (fun state _ => (state.1, none))
          (.goto fun _ => .vertex (MachineRegularVertexBlock.dummyEntry internalDegree
            MachineRegularOriginalBody.degree_positive)))
        (.load (fun state => (state.1, none))
          (.goto fun _ => .cleanup MachineRegularOwnerCleanup.entry)))
  | .vertex l => Lift.statement core Label.vertex (some .bump)
      vertexStates (MachineRegularOriginalBody.vertexSource l)
  | .bump => .push (core 1) (fun _ => true)
      (.push (core 3) (fun _ => true) (.goto fun _ => .loop))
  | .cleanup l => MachineRegularOwnerCleanup.instruction Label.cleanup none l

def working (data : Data) (fuel saved : List Bool) : Tape → List Bool
  | .inl k => MachineRegularOriginalBody.frame data k
  | .inr i => if i = 0 then fuel else saved

def frame (data : Data) : Tape → List Bool := working data [] []

def cfg (H : BaseTable) (label : Option Label) (data : Data) : TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data⟩

def initialData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val)
  owner := encodeWord v.val
  localRank := []
  count := []
  offset := encodeWord (PreprocessingPaddingOffsets.offset (padding t) v.val)
  darts := encodeWord t.darts
  rotor := []
  output := output
  padding := []
  level := []

def metadataData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data :=
  MachineRegularMetadata.cloudData t v (initialData t v output)

def seededData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data :=
  { metadataData t v output with localRank := encodeWord (cloudSize t v) }

def ownerBits (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) : List Bool :=
  (List.ofFn (PreprocessingRegularWords.dummyVertexBits t (padding t) (familyCloudTable H t) v)).flatten

def finalData (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : Data :=
  { initialData t v output with
    globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val + padding t v)
    offset := encodeWord (PreprocessingPaddingOffsets.offset (padding t) v.val + padding t v)
    output := output ++ ownerBits H t v }

end BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody

end OAI
