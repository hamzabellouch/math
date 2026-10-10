import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachinePaddedExpanderFamilyBoundsLemmas

namespace OAI

/-!
# Materializing a cloud rotor inside the regularization machine

Core tape 4 contains the unary cloud size and core tape 7 receives the complete
forward rotor table. The actual family computation runs on private tapes;
three retained unary words are then physically drained. All other core tapes
are preserved and all private tapes are empty on return.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

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

/-- Unused private shadows of the two public roles remain empty. -/
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

/-- Every size-dependent operation is performed by the checked native program.
The entry load only resets the finite control state. -/
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

/-- The only retained native work words are the two sizes and the exhausted level. -/
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

/-- The actual native family run, including geometric-level computation. -/
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

/-- Every retained private symbol is physically popped. -/
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

/-- Complete clean-frame execution, from the caller's actual unary request.
No callback, table-construction premise, or caller-supplied runtime is assumed. -/
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

/-- Direct embedding of the entire helper into another finite program. -/
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

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

end OAI
