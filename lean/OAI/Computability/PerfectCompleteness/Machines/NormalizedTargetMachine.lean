import OAI.Computability.PerfectCompleteness.Machines.NormalizedTargetTapeBound
import OAI.Computability.PerfectCompleteness.Reduction.NormalizedTargetInitialization
import OAI.Computability.PerfectCompleteness.Reduction.TargetFinalizeBound
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI


namespace PerfectCompleteness.NormalizedTargetMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

abbrev Tape (branch : Nat → Nat) (n t : Nat) :=
  SignedTupleLayout.Tape (TreeCanonical.locationCount branch n t) (Fin 4)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "Arena" => Tape branch n t

def tapeEnumeration (branch : Nat → Nat) (n t : Nat) :
    Fin (Fintype.card (Tape branch n t)) ≃ Tape branch n t :=
  (Fintype.equivFin (Tape branch n t)).symm

def finalizerTape (branch : Nat → Nat) (n t : Nat) : Fin 4 → Tape branch n t
  | 0 => .edgeWork 7
  | 1 => .edgeCount
  | 2 => .extra 2
  | 3 => .extra 3

theorem finalizerTape_injective (branch : Nat → Nat) (n t : Nat) :
    Function.Injective (finalizerTape branch n t) := by
  intro i j same
  fin_cases i <;> fin_cases j <;> simp [finalizerTape] at same ⊢

variable (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "Desc" => SignedCompletionSchedule.Descriptor
  (rows := rows) (repeats := repeats)
  (CanonicalLocalCompletion.alphabet_positive width δ)
  (CanonicalLocalCompletion.partitionWidth_le_alphabet width δ)
local notation "Native" => ExactTargetOdometer.NativeLabel
  (branch := branch) (n := n) (t := t) rows repeats hn hbranch hrows δ (Fin 4)
local notation "Final" => TargetFinalizeMachine.Labels
  (tapeEnumeration branch n t) (finalizerTape branch n t 3)

abbrev Control := ExactTargetOdometer.Control (branch := branch) (n := n) (t := t)
  rows repeats δ

abbrev Ambient := ExactTargetOdometer.Ambient (branch := branch) (n := n) (t := t)
  rows repeats δ

abbrev Label := NormalizedTargetInitialization.Label ⊕ (Native ⊕ Final)

def initialControl : Control (branch := branch) (n := n) (t := t) rows repeats δ :=
  SignedTupleLayout.clean («width» := width) («Desc» := Desc) ()

def initialAmbient : Ambient (branch := branch) (n := n) (t := t) rows repeats δ :=
  (initialControl (branch := branch) (n := n) (t := t) rows repeats δ).1

local notation "Labels" => Label (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ
local notation "Registers" => Control (branch := branch) (n := n) (t := t) rows repeats δ
local notation "initial" => initialControl (branch := branch) (n := n) (t := t) rows repeats δ
local notation "ambient" => initialAmbient (branch := branch) (n := n) (t := t) rows repeats δ

def initLabel (label : NormalizedTargetInitialization.Label) : Labels := .inl label

def driverLabel (label : Native) : Labels := .inr (.inl label)

def finalizerLabel (label : Final) : Labels := .inr (.inr label)

local notation "liftInit" => initLabel (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ
local notation "liftDriver" => driverLabel (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ
local notation "liftFinal" => finalizerLabel (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ
local notation "nativeProgram" => ExactTargetOdometer.program
  (branch := branch) (n := n) (t := t) (Extra := Fin 4)
  rows repeats hn hbranch hrows δ
local notation "nativeEntry" => ExactTargetOdometer.body
  (branch := branch) (n := n) (t := t) (Extra := Fin 4)
  rows repeats hn hbranch hrows δ

def program : Labels → TM2.Stmt (fun _ : Arena => Bool) Labels Registers
  | .inl label => NormalizedTargetInitialization.instruction liftInit
      (some (liftDriver nativeEntry)) none label
  | .inr (.inl label) => MachineSubroutine.statement liftDriver
      (some (liftFinal .reverse)) (nativeProgram label)
  | .inr (.inr label) => TargetFinalizeMachine.instruction q
      (tapeEnumeration branch n t) (finalizerTape branch n t) ambient liftFinal label

local notation "runProgram" => program (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ

def machine : FinTM2 where
  K := Arena
  k₀ := .source .table
  k₁ := .extra 3
  Γ _ := Bool
  Λ := Labels
  main := liftInit .seed
  σ := Registers
  initialState := initial
  m := runProgram

local notation "tm" => machine (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ

def configuration (label : Option Labels) (tapes : Arena → List Bool) : (tm).Cfg :=
  ⟨label, initial, tapes⟩

local notation "cfg" => configuration (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ

def returnInTime (tapes : Arena → List Bool) :
    StateTransition.EvalsToInTime (TM2.step runProgram)
      (cfg (some (liftDriver .exit)) tapes)
      (some (cfg (some (liftFinal .reverse)) tapes)) 1 where
  steps := 1
  evals_in_steps := rfl
  steps_le_m := Nat.le_refl 1

local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "finalData" => NormalizedTargetTapeBound.finalData
  (t := t) rows repeats hn hbranch hrows δ
local notation "finalTapes" => NormalizedTargetTapeBound.finalTapes
  (t := t) rows repeats hn hbranch hrows δ
local notation "output" => NormalizedTarget.outputBits (t := t) rows repeats hn hbranch hrows δ

theorem header_body_eq_outputBits (input : NormalizedSourceInput.Input) :
    encodeWords [(finalData input).count, (finalData input).count,
        q, (finalData input).count] ++ (finalData input).reversedOutput.reverse =
      output input := by
  simpa only [NormalizedTargetTapeBound.finalData, SignedTupleSemantics.dataOfPrefix,
    List.append_nil, List.reverse_reverse, NormalizedTarget.outputBits,
    NormalizedTarget.construct] using
    (ExactTargetOnlineEncoding.target_gameBits (t := t)
      (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ).symm

def initializeInTime (input : NormalizedSourceInput.Input) :
    StateTransition.EvalsToInTime (TM2.step runProgram)
      (cfg (some (liftInit .seed)) (NormalizedTargetInitialization.inputTapes input))
      (some (cfg (some (liftDriver nativeEntry))
        (NormalizedTargetInitialization.readyTapes input)))
      (4 * ((NormalizedSourceInput.bits input).length + 1)) := by
  exact NormalizedTargetInitialization.initializeInTime liftInit
    (some (liftDriver nativeEntry)) none runProgram (fun _ => rfl) input ambient none

def enumerateInTime (input : NormalizedSourceInput.Input) :
    StateTransition.EvalsToInTime (TM2.step runProgram)
      (cfg (some (liftDriver nativeEntry)) (NormalizedTargetInitialization.readyTapes input))
      (some (cfg (some (liftDriver .exit)) (finalTapes input)))
      (ExactTargetOdometer.timeBound (t := t) rows repeats hn hbranch hrows δ
        (NormalizedSourceInput.bits input).length) := by
  have run := MachineSubroutine.execution liftDriver (some (liftFinal .reverse))
    nativeProgram runProgram (fun _ => rfl)
    (ExactTargetOdometer.targetInTimePolynomial rows repeats hn hbranch hrows δ input []
      (fun _ : Fin 4 => []))
  rw [NormalizedTargetInitialization.ready_eq_native (branch := branch) (n := n) (t := t) input]
  delta NormalizedTargetInitialization.zeroDigits
  simpa only [configuration, initialControl,
    MachineSubroutine.configuration, MachineSubroutine.label,
    ExactTargetOdometer.configuration, NormalizedTargetInitialization.zeroDigits,
    NormalizedTargetTapeBound.finalTapes, NormalizedTargetTapeBound.finalData,
    SignedTupleSemantics.dataOfPrefix, ExactTargetOnlineEncoding.leftKeys,
    ExactTargetOnlineEncoding.rightKeys, List.map_nil, List.flatMap_nil,
    List.reverse_nil, List.nil_append, List.length_nil] using! run

def finalizeBudget (size : Nat) : Nat :=
  (15 + Fintype.card Arena * (q + 9)) *
    (TargetTapeEnvelope.coeff width q D * (size + 1) ^ (2 * width + 2) + 1)

def finalizeInTime (input : NormalizedSourceInput.Input) :
    StateTransition.EvalsToInTime (TM2.step runProgram)
      (cfg (some (liftFinal .reverse)) (finalTapes input))
      (some (cfg none (MachineDrainMany.haltTapes (.extra 3) (output input))))
      (finalizeBudget (t := t) rows repeats hn hbranch hrows δ (NormalizedSourceInput.bits input).length) := by
  have run := TargetFinalizeBound.finalizeInTime q (tapeEnumeration branch n t)
    (finalizerTape branch n t) (finalizerTape_injective branch n t) ambient liftFinal
    runProgram (fun _ => rfl) (finalTapes input) ambient none (finalData input).count
    (finalData input).reversedOutput.reverse
    (by simp only [finalizerTape, NormalizedTargetTapeBound.finalTapes,
      ExactTargetOdometer.nativeTapes_output, List.reverse_reverse])
    (by simp only [finalizerTape, NormalizedTargetTapeBound.finalTapes,
      ExactTargetOdometer.nativeTapes_count])
    (by simp only [finalizerTape, NormalizedTargetTapeBound.finalTapes,
      ExactTargetOdometer.nativeTapes_extra])
    (by simp only [finalizerTape, NormalizedTargetTapeBound.finalTapes,
      ExactTargetOdometer.nativeTapes_extra])
    (TargetTapeEnvelope.coeff width q D *
      ((NormalizedSourceInput.bits input).length + 1) ^ (2 * width + 2))
    (NormalizedTargetTapeBound.finalTapes_length_le_polynomial
      rows repeats hn hbranch hrows δ input)
  rw [header_body_eq_outputBits rows repeats hn hbranch hrows δ input] at run
  exact run

def totalBudget (size : Nat) : Nat :=
  4 * (size + 1) + ExactTargetOdometer.timeBound (t := t) rows repeats hn hbranch hrows δ size + 1 +
    finalizeBudget (t := t) rows repeats hn hbranch hrows δ size

def totalInTime (input : NormalizedSourceInput.Input) :
    StateTransition.EvalsToInTime (TM2.step runProgram)
      (cfg (some (liftInit .seed)) (NormalizedTargetInitialization.inputTapes input))
      (some (cfg none (MachineDrainMany.haltTapes (.extra 3) (output input))))
      (totalBudget (t := t) rows repeats hn hbranch hrows δ (NormalizedSourceInput.bits input).length) := by
  have first := StateTransition.EvalsToInTime.trans (TM2.step runProgram) _ _ _ _ _
    (initializeInTime rows repeats hn hbranch hrows δ input)
    (enumerateInTime rows repeats hn hbranch hrows δ input)
  have second := StateTransition.EvalsToInTime.trans (TM2.step runProgram) _ _ _ _ _
    first (returnInTime rows repeats hn hbranch hrows δ (finalTapes input))
  have full := StateTransition.EvalsToInTime.trans (TM2.step runProgram) _ _ _ _ _
    second (finalizeInTime rows repeats hn hbranch hrows δ input)
  simpa only [totalBudget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def time : Polynomial Nat :=
  4 * (Polynomial.X + 1) +
    Polynomial.C (SignedCostEnvelope.bodyCoeff width D + 2 * width) *
      (Polynomial.X + 1) ^ (SignedCostEnvelope.degree width + width) + 1 +
    Polynomial.C (15 + Fintype.card Arena * (q + 9)) *
      (Polynomial.C (TargetTapeEnvelope.coeff width q D) *
        (Polynomial.X + 1) ^ (2 * width + 2) + 1)

theorem time_eval (size : Nat) :
    (time (t := t) rows repeats hn hbranch hrows δ).eval size =
      totalBudget (t := t) rows repeats hn hbranch hrows δ size := by
  simp [time, totalBudget, finalizeBudget, ExactTargetOdometer.timeBound]

private theorem initList_eq (input : NormalizedSourceInput.Input) :
    initList tm (NormalizedSourceInput.bits input) =
      cfg (some (liftInit .seed)) (NormalizedTargetInitialization.inputTapes input) := by
  unfold initList configuration
  congr 1
  funext key
  cases key with
  | source source =>
      cases source <;> simp [machine, NormalizedTargetInitialization.inputTapes]
      rfl
  | current i => simp [machine, NormalizedTargetInitialization.inputTapes]
  | remaining i => simp [machine, NormalizedTargetInitialization.inputTapes]
  | encodedVariable i j => simp [machine, NormalizedTargetInitialization.inputTapes]
  | adapterScratch => simp [machine, NormalizedTargetInitialization.inputTapes]
  | edgeWork j => simp [machine, NormalizedTargetInitialization.inputTapes]
  | edgeCount => simp [machine, NormalizedTargetInitialization.inputTapes]
  | extra j => simp [machine, NormalizedTargetInitialization.inputTapes]

private theorem haltList_eq (word : List Bool) :
    haltList tm word = cfg none (MachineDrainMany.haltTapes (.extra 3) word) := by
  unfold haltList configuration
  congr 1

def outputsInTime (input : NormalizedSourceInput.Input) :
    TM2OutputsInTime tm (NormalizedSourceInput.bits input) (some (output input))
      (totalBudget (t := t) rows repeats hn hbranch hrows δ
        (NormalizedSourceInput.bits input).length) := by
  change StateTransition.EvalsToInTime (TM2.step runProgram)
    (initList tm (NormalizedSourceInput.bits input))
    (some (haltList tm (output input))) _
  rw [initList_eq, haltList_eq]
  exact totalInTime rows repeats hn hbranch hrows δ input

def computation :
    TM2ComputableInPolyTime NormalizedTarget.inputBits (id : List Bool → List Bool)
      (NormalizedTarget.outputBits (t := t) rows repeats hn hbranch hrows δ) where
  «tm» := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time (t := t) rows repeats hn hbranch hrows δ
  outputsFun input := by
    change TM2OutputsInTime tm ((NormalizedTarget.inputBits input).map id)
      (some ((output input).map id))
      ((time (t := t) rows repeats hn hbranch hrows δ).eval
        (NormalizedTarget.inputBits input).length)
    have hi := @List.map_id ((tm).Γ (tm).k₀) (NormalizedSourceInput.bits input)
    have ho := @List.map_id ((tm).Γ (tm).k₁) (output input)
    simpa only [hi, ho, time_eval, NormalizedTarget.inputBits] using
      outputsInTime rows repeats hn hbranch hrows δ input

def targetComputation :
    TM2ComputableInPolyTime NormalizedSourceInput.bits Encoding.gameBits
      (NormalizedTarget.construct (t := t) rows repeats hn hbranch hrows δ) where
  «tm» := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time (t := t) rows repeats hn hbranch hrows δ
  outputsFun input := by
    change TM2OutputsInTime tm ((NormalizedSourceInput.bits input).map id)
      (some ((output input).map id))
      ((time (t := t) rows repeats hn hbranch hrows δ).eval
        (NormalizedSourceInput.bits input).length)
    have hi := @List.map_id ((tm).Γ (tm).k₀) (NormalizedSourceInput.bits input)
    have ho := @List.map_id ((tm).Γ (tm).k₁) (output input)
    simpa only [hi, ho, time_eval] using
      outputsInTime (t := t) rows repeats hn hbranch hrows δ input

theorem workAlphabet_finite (key : (tm).K) : Finite ((tm).Γ key) := by
  change Finite Bool
  infer_instance

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet tm :=
  MachineFiniteAlphabet.of_bool tm (fun _ => rfl)

end
end PerfectCompleteness.NormalizedTargetMachine

end OAI
