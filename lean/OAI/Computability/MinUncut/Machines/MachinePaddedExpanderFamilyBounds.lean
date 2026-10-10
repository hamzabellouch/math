import Mathlib
import OAI.Computability.MinUncut.Machines.MachineExpanderFamilyCycle

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def timeCoefficient : Nat :=
  MachineExpanderFamilyBounds.inputCoefficient + PCP.ExpanderFamily.growth + 29

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C timeCoefficient * Polynomial.X^5

theorem timePolynomial_encoding (k : Nat) :
    timePolynomial.eval (encodeWord k).length = timeCoefficient * (k + 1)^5 := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, encodeWord_length]

theorem ceilingCost_le (g k : Nat) :
    (MachineCeilingPower.timePolynomial g).eval (encodeWord k).length ≤
      (g + 29) * (k + 1)^5 := by
  rw [MachineCeilingPower.timePolynomial_encoding]
  have squareBound : (k + 1)^2 ≤ (k + 1)^5 :=
    Nat.pow_le_pow_right (Nat.succ_pos k) (by decide)
  have linearBound : k + 1 ≤ (k + 1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_pos k) (show 1 ≤ 5 by decide)
  have constantBound : 1 ≤ (k + 1)^5 := by omega
  have squareCost := Nat.mul_le_mul_left (g + 8) squareBound
  have linearCost := Nat.mul_le_mul_left 18 linearBound
  have constantCost := Nat.mul_le_mul_left 3 constantBound
  unfold MachineCeilingPower.timeBound
  nlinarith only [squareCost, linearCost, constantCost]

theorem combinedCost_le (k : Nat) :
    (MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord k).length +
      MachineExpanderFamilyBounds.inputCoefficient * (k + 1)^5 ≤
        timePolynomial.eval (encodeWord k).length := by
  rw [timePolynomial_encoding]
  have h := ceilingCost_le PCP.ExpanderFamily.growth k
  unfold timeCoefficient
  nlinarith only [h]

theorem familyCost_le
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    (MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord k).length +
      MachineExpanderFamilyBounds.familyBudget H (PCP.PreprocessingLevels.boundedLevel k) ≤
        timePolynomial.eval (encodeWord k).length := by
  exact (Nat.add_le_add_left
    (MachineExpanderFamilyBounds.familyBudget_at_boundedLevel_le H k) _).trans
      (combinedCost_le k)

def outputWord
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    List Bool :=
  encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel k)))

def outputCoefficient : Nat :=
  (PCP.ExpanderFamily.growth * degree PCP.Expanders.baseDegree + 1)^2

theorem outputWord_length_le
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    (outputWord H k).length ≤ outputCoefficient * (k + 1)^2 := by
  let q := degree PCP.Expanders.baseDegree
  let N := vertexCount q (PCP.PreprocessingLevels.boundedLevel k)
  have sizeBound : N ≤ PCP.ExpanderFamily.growth * (k + 1) := by
    change vertexCount (PCP.Expanders.baseDegree * PCP.Expanders.baseDegree)
      (PCP.PreprocessingLevels.boundedLevel k) ≤ _
    rw [PCP.PreprocessingLevels.table_vertexCount_eq_paddedSize]
    exact MachineExpanderFamilyBounds.paddedSize_le_succ_input k
  have rowBound := Nat.mul_le_mul_right q sizeBound
  have rowSuccBound : N * q + 1 ≤ (PCP.ExpanderFamily.growth * q + 1) * (k + 1) := by
    nlinarith only [rowBound, Nat.zero_le k]
  have lengthBound : (outputWord H k).length ≤ (N * q) * (N * q + 1) :=
    encode_rotationWords_length_le (family H (PCP.PreprocessingLevels.boundedLevel k))
  calc
    _ ≤ (N * q + 1)^2 := by nlinarith only [lengthBound, Nat.zero_le (N * q)]
    _ ≤ ((PCP.ExpanderFamily.growth * q + 1) * (k + 1))^2 :=
      Nat.pow_le_pow_left rowSuccBound 2
    _ = _ := by unfold outputCoefficient; dsimp [q]; ring

end MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

end
section
namespace MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open MachineCloudPadding
open MachineComposition


variable {ρ : Type} [Fintype ρ]

noncomputable def ceilingInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some main, initialState state register, initialTapes requested⟩
      (some ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩)
      ((MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord requested).length) := by
  let original := MachineCeilingPower.paddingInTime requested state register
  let renamed := MachineStateEquiv.execution (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth) original
  let placed := liftExecutionInTime (TM2.step (ceilingSource (ρ := ρ)))
    (TM2.step (program H))
    (Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => []))
    (Placement.step_simulation ceilingTape ceilingView ceilingView_left ceilingView_right
      ceilingLabel (some familyEntry) (fun _ => []) (ceilingSource (ρ := ρ))
      (program H) (program_ceiling H)) renamed
  have initialEq := ceiling_initial_configuration requested state register
  have finalEq := ceiling_handoff_configuration requested state
  unfold ceilingInput at initialEq
  unfold ceilingOutput at finalEq
  simpa only [initialEq, finalEq] using placed

noncomputable def materializeInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩
      (some ⟨none, finalState H state, finalTapes H requested⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (requested + 1)^5) := by
  let original := MachineExpanderFamily.paddedFamilyInTime H requested state []
  let boolean := MachineAlphabetTransport.executionInTime MachineExpanderFamily.alphabet_eq
    (MachineExpanderFamily.program MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) original
  let framed := MachineStateFrame.frameExecution
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) (false, (none : Option Bool)) boolean
  let placed := liftExecutionInTime (TM2.step (familySource H)) (TM2.step (program H))
    (Placement.configuration familyView familyLabel none (retainedFrame requested))
    (Placement.step_simulation familyTape familyView familyView_left familyView_right
      familyLabel none (retainedFrame requested) (familySource H) (program H)
      (program_family H)) framed
  simpa only [family_initial_configuration, family_final_configuration] using placed

noncomputable def paddedInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some main, initialState state register, initialTapes requested⟩
      (some ⟨none, finalState H state, finalTapes H requested⟩)
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord requested).length) := by
  let first := ceilingInTime H requested state register
  let second := materializeInTime H requested state
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H))
    _ _ _ _ _ first second
  exact
    { toEvalsTo := all.toEvalsTo
      steps_le_m := all.steps_le_m.trans
        (by simpa only [Nat.add_comm] using
          MachinePaddedExpanderFamilyBounds.combinedCost_le requested) }

noncomputable def placedInTime {K Λ : Type} [DecidableEq K]
    (tape : Tape → K) (view : K → Option Tape)
    (left : ∀ t, view (tape t) = some t)
    (right : ∀ j t, view j = some t → tape t = j)
    (labels : Label → Λ) (exit : Option Λ) (extra : K → List Bool)
    (H : SmallTable) (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ))
    (code : ∀ l, target (labels l) = Placement.statement tape labels exit (program H l))
    (requested : Nat) (state : MachineExpanderFamily.State ρ fixedDegree)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      (Placement.configuration view labels exit extra
        ⟨some main, initialState state register, initialTapes requested⟩)
      (some (Placement.configuration view labels exit extra
        ⟨none, finalState H state, finalTapes H requested⟩))
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord requested).length) :=
  liftExecutionInTime (TM2.step (program H)) (TM2.step target)
    (Placement.configuration view labels exit extra)
    (Placement.step_simulation tape view left right labels exit extra (program H) target code)
    (paddedInTime H requested state register)

end MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamily

end
section
namespace MinUncutGames.Foundations.Complexity.MachineRegularFamily

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

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
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

end MinUncutGames.Foundations.Complexity.MachineRegularFamily

end
section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def zeroTest (operand : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek operand (fun s head => (s.1, head))
    (.load (fun s => ((s.1.1, !(s.2.getD false)), none))
      (Reduction.MachineTransfer.exitAt operand exit))

theorem zeroTestTrace (operand : K) (testLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atTest : program testLabel = zeroTest operand exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (word : base operand = encodeWord n ++ suffix)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[1]
      (some ⟨some testLabel, ((ambient, flag), register), base⟩) =
      some ⟨exit, ((ambient, decide (n = 0)), none), base⟩ := by
  change some (TM2.stepAux (program testLabel) _ _) = _
  rw [atTest]
  cases n <;> cases exit <;>
    simp [zeroTest, TM2.stepAux, word, encodeWord, List.replicate_succ,
      Reduction.MachineTransfer.exitAt]

def tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (slots 0) left) (slots 1) right) (slots 2) savedLeft) (slots 3) savedRight

@[simp] theorem tapes_left (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 0) = left := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_right (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 1) = right := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedLeft (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 2) = savedLeft := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedRight (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 3) = savedRight := by
  simp [tapes]

@[simp] theorem update_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacement : List Bool) (i : Fin 4) :
    Function.update (tapes slots base left right savedLeft savedRight) (slots i) replacement =
      tapes slots base (if i = 0 then replacement else left)
        (if i = 1 then replacement else right) (if i = 2 then replacement else savedLeft)
        (if i = 3 then replacement else savedRight) := by
  fin_cases i <;> funext k
  all_goals
    by_cases h₀ : k = slots 0
    · subst k; simp [tapes, slots.injective.eq_iff]
    · by_cases h₁ : k = slots 1
      · subst k; simp [tapes, slots.injective.eq_iff]
      · by_cases h₂ : k = slots 2
        · subst k; simp [tapes, slots.injective.eq_iff]
        · by_cases h₃ : k = slots 3
          · subst k; simp [tapes, slots.injective.eq_iff]
          · simp [tapes, h₀, h₁, h₂, h₃]

@[simp] theorem tapes_self (slots : Fin 4 ↪ K) (base : K → List Bool) :
    tapes slots base (base (slots 0)) (base (slots 1)) (base (slots 2)) (base (slots 3)) = base := by
  simp [tapes]

def stop (result : Bool) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .load (fun s => ((s.1.1, result), none)) (.goto fun _ => restoreLabel)

def scan (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek (slots 0) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (.pop (slots 0) (fun s _ => s)
            (.pop (slots 1) (fun s _ => s)
              (.push (slots 2) (fun _ => true)
                (.push (slots 3) (fun _ => true) (.goto fun _ => scanLabel)))))
          (stop false restoreLabel)))
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (stop true restoreLabel) (stop false restoreLabel))))

theorem scan_step_zero_left (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, decide (0 < b)), none),
        tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  cases b <;> simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_zero_right (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, false), none),
        tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_succ (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord (b + 1) ++ rightSuffix)
        savedLeft savedRight⟩ =
      some ⟨some scanLabel, ((ambient, flag), some true),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix)
          (true :: savedLeft) (true :: savedRight)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scanTrace (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[min a b + 1]
      (some ⟨some scanLabel, ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩) =
      some ⟨some restoreLabel, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord (a - b) ++ leftSuffix) (encodeWord (b - a) ++ rightSuffix)
          (List.replicate (min a b) true ++ savedLeft) (List.replicate (min a b) true ++ savedRight)⟩ := by
  induction a generalizing b savedLeft savedRight register with
  | zero =>
    simpa using scan_step_zero_left slots scanLabel restoreLabel program atScan base b
      leftSuffix rightSuffix savedLeft savedRight ambient flag register
  | succ a ih =>
    cases b with
    | zero =>
      simpa using scan_step_zero_right slots scanLabel restoreLabel program atScan base a
        leftSuffix rightSuffix savedLeft savedRight ambient flag register
    | succ b =>
      have hm : min (a + 1) (b + 1) = min a b + 1 := by omega
      rw [hm, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ slots scanLabel restoreLabel program atScan, ih]
      have hsave (xs : List Bool) :
          List.replicate (min a b) true ++ true :: xs =
            List.replicate (min a b + 1) true ++ xs := by
        simp [List.replicate_add, List.append_assoc]
      simp only [hsave, Nat.add_sub_add_right, Nat.add_lt_add_iff_right]

@[simp] theorem transferLeft_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementLeft : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 2) (slots 0)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementLeft =
      tapes slots base replacementLeft right replacementSaved savedRight := by
  simp [Reduction.MachineTransfer.tapesAt]

@[simp] theorem transferRight_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementRight : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 3) (slots 1)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementRight =
      tapes slots base left replacementRight savedLeft replacementSaved := by
  simp [Reduction.MachineTransfer.tapesAt]

inductive Label where
  | scan
  | restoreLeft
  | restoreRight
  deriving DecidableEq

instance : Fintype Label where
  elems := { .scan, .restoreLeft, .restoreRight }
  complete l := by cases l <;> simp

def statement (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .scan => scan slots (labels .scan) (labels .restoreLeft)
  | .restoreLeft => Reduction.MachineTransfer.loopAt (slots 2) (slots 0) id false
      (labels .restoreLeft) (some (labels .restoreRight))
  | .restoreRight => Reduction.MachineTransfer.loopAt (slots 3) (slots 1) id false
      (labels .restoreRight) exit

def steps (a b : Nat) : Nat := 3 * (min a b + 1)

theorem comparisonTrace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨exit, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩ := by
  have hscan := scanTrace slots (labels .scan) (labels .restoreLeft) program (atLabels .scan)
    base a b leftSuffix rightSuffix [] [] ambient flag register
  simp only [List.append_nil] at hscan
  have hwordLeft : List.replicate (min a b) true ++ (encodeWord (a - b) ++ leftSuffix) =
      encodeWord a ++ leftSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (a - b) = a by omega]
  have hwordRight : List.replicate (min a b) true ++ (encodeWord (b - a) ++ rightSuffix) =
      encodeWord b ++ rightSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (b - a) = b by omega]
  let middle := tapes slots base (encodeWord (a - b) ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) (List.replicate (min a b) true) (List.replicate (min a b) true)
  have hleft := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 2) (slots 0)
    (slots.injective.ne (by decide)) id false (labels .restoreLeft) (some (labels .restoreRight))
    program (by simpa only [statement] using atLabels .restoreLeft)
    middle (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(middle (slots 2)).length + 1]
    (some ⟨some (labels .restoreLeft), ((ambient, decide (a < b)), none), middle⟩) = _ at hleft
  simp only [middle, tapes_savedLeft, tapes_left, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordLeft, transferLeft_tapes] at hleft
  let afterLeft := tapes slots base (encodeWord a ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) [] (List.replicate (min a b) true)
  have hright := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 3) (slots 1)
    (slots.injective.ne (by decide)) id false (labels .restoreRight) exit
    program (by simpa only [statement] using atLabels .restoreRight)
    afterLeft (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(afterLeft (slots 3)).length + 1]
    (some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩) = _ at hright
  simp only [afterLeft, tapes_savedRight, tapes_right, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordRight, transferRight_tapes] at hright
  have hfirst : (advance (TM2.step program))^[(min a b + 1) + (min a b + 1)]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩ := by
    rw [Function.iterate_add_apply, hscan]
    exact hleft
  rw [show steps a b = (min a b + 1) + ((min a b + 1) + (min a b + 1)) by
    unfold steps; omega, Function.iterate_add_apply, hfirst]
  exact hright

theorem lessThanTrace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (slots 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (slots 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .scan), ((ambient, flag), register), base⟩) =
      some ⟨exit, ((ambient, decide (a < b)), none), base⟩ := by
  have h := comparisonTrace slots labels exit program atLabels base a b leftSuffix rightSuffix
    ambient flag register
  have hframe := tapes_self slots base
  rw [leftWord, rightWord, leftEmpty, rightEmpty] at hframe
  rw [hframe] at h
  exact h

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 3 * Polynomial.X + Polynomial.C 3

theorem steps_le_time (a b : Nat) : steps a b ≤ timePolynomial.eval (a + b) := by
  simp only [steps, timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  have := Nat.min_le_left a b
  omega

def lessThanInPolynomialTime (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (slots 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (slots 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), ((ambient, flag), register), base⟩
      (some ⟨exit, ((ambient, decide (a < b)), none), base⟩) (timePolynomial.eval (a + b)) where
  steps := steps a b
  evals_in_steps := lessThanTrace slots labels exit program atLabels base a b leftSuffix rightSuffix
    leftWord rightWord leftEmpty rightEmpty ambient flag register
  steps_le_m := steps_le_time a b

abbrev machine : Turing.FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := .scan
  σ := State Unit
  initialState := (((), false), none)
  m := statement (Function.Embedding.refl _) id none

def machineInPolynomialTime (base : Fin 4 → List Bool) (a b : Nat)
    (leftSuffix rightSuffix : List Bool)
    (leftWord : base 0 = encodeWord a ++ leftSuffix)
    (rightWord : base 1 = encodeWord b ++ rightSuffix)
    (leftEmpty : base 2 = []) (rightEmpty : base 3 = []) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .scan, (((), false), none), base⟩
      (some ⟨none, (((), decide (a < b)), none), base⟩) (timePolynomial.eval (a + b)) :=
  lessThanInPolynomialTime (Function.Embedding.refl _) id none machine.m (fun _ => rfl)
    base a b leftSuffix rightSuffix leftWord rightWord leftEmpty rightEmpty () false none

end MinUncutGames.Foundations.Complexity.MachineUnaryLessAt

end

end OAI
