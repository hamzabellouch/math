import OAI.Computability.PerfectCompleteness.Machines.TupleEnumerationMachine
import OAI.Computability.PerfectCompleteness.Machines.TupleInitializationMachine
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas

namespace OAI


namespace PerfectCompleteness.TupleIndexMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open scoped BigOperators

abbrev Tape (width : Nat) := TupleEnumerationMachine.Tape width Unit
abbrev Register := Unit × Option Bool

def source {width : Nat} : Tape width := .extra (.inr ())

def cleanupTapes (width : Nat) : List (Tape width) :=
  [.scratch, source] ++ TupleInitializationMachine.currentDestinations width Unit ++
    TupleInitializationMachine.remainingDestinations width Unit

abbrev Label (width : Nat) := TupleInitializationMachine.Label ⊕
  (TupleEnumerationMachine.Label width ⊕ MachineDrainMany.Label (cleanupTapes width))

variable {width : Nat}

def initLabel (label : TupleInitializationMachine.Label) : Label width := .inl label

def enumerationLabel (label : TupleEnumerationMachine.Label width) : Label width :=
  .inr (.inl label)

def cleanupLabel (label : MachineDrainMany.Label (cleanupTapes width)) : Label width :=
  .inr (.inr label)

def cleanupEntry : Option (Label width) :=
  MachineDrainMany.entry (cleanupTapes width) cleanupLabel none

def program : Label width → TM2.Stmt (fun _ : Tape width => Bool) (Label width) Register
  | .inl label => TupleInitializationMachine.arenaInstruction () initLabel
      (some (enumerationLabel TupleEnumerationMachine.body)) label
  | .inr (.inl label) => MachineSubroutine.statement enumerationLabel cleanupEntry
      (TupleEnumerationMachine.program label)
  | .inr (.inr label) => MachineDrainMany.instruction (cleanupTapes width) cleanupLabel none label

def machine (width : Nat) : FinTM2 where
  K := Tape width
  k₀ := source
  k₁ := .output
  Γ _ := Bool
  Λ := Label width
  main := initLabel .seed
  σ := Register
  initialState := ((), none)
  m := program

def cfg (label : Option (Label width)) (tapes : Tape width → List Bool) :
    (machine width).Cfg := ⟨label, ((), none), tapes⟩

def inputTapes (radix : Nat) : Tape width → List Bool :=
  fun tape => if tape = source then encodeWord radix else []

def output (width radix : Nat) : List Bool :=
  TupleEnumerationMachine.outputBlock radix width (fun _ : Fin width => 0)

def readyTapes (radix : Nat) : Tape width → List Bool :=
  TupleEnumerationMachine.tapes radix (fun _ => 0) [] (fun _ => [])

def emittedTapes (radix : Nat) : Tape width → List Bool :=
  TupleEnumerationMachine.tapes radix (fun _ => 0) (output width radix) (fun _ => [])

theorem output_eq (width radix : Nat) :
    output width radix =
      (MachineTupleOdometer.tupleOrder radix width).reverse.flatMap
        (fun tuple => encodeWords (List.ofFn (fun i => (tuple i).val))) :=
  TupleEnumerationMachine.outputBlock_all (width := width) radix

private theorem initialized_eq (radix : Nat) :
    TupleInitializationMachine.arenaInitializedTapes () (inputTapes (width := width) radix)
      (radix - 1) [] = readyTapes radix := by
  funext tape
  cases tape with
  | current i =>
      rw [TupleInitializationMachine.arenaInitializedTapes_current]
      · rfl
      · simp [inputTapes, source]
  | scratch =>
      rw [TupleInitializationMachine.arenaInitializedTapes_scratch]
      simp [inputTapes, source, readyTapes, TupleEnumerationMachine.tapes]
  | output =>
      rw [TupleInitializationMachine.arenaInitializedTapes_output]
      simp [inputTapes, source, readyTapes, TupleEnumerationMachine.tapes]
  | extra value =>
      cases value with
      | inl i =>
          rw [TupleInitializationMachine.arenaInitializedTapes_remaining]
          · simp only [readyTapes, TupleEnumerationMachine.tapes, Nat.sub_zero]
          · simp [inputTapes, source]
      | inr value =>
          cases value
          rw [TupleInitializationMachine.arenaInitializedTapes_source]
          rfl

def initializeInTime (radix : Nat) (positive : 0 < radix) :
    StateTransition.EvalsToInTime (TM2.step (program (width := width)))
      (cfg (some (initLabel .seed)) (inputTapes radix))
      (some (cfg (some (enumerationLabel TupleEnumerationMachine.body)) (readyTapes radix)))
      (radix + 1) := by
  have run := TupleInitializationMachine.arenaInitializeInTime (width := width) (Λ := Label width) () initLabel
    (some (enumerationLabel TupleEnumerationMachine.body)) program (fun _ => rfl)
    (inputTapes radix) () radix positive []
    (by simp [inputTapes, source])
  simpa only [cfg, TupleInitializationMachine.clean, initialized_eq] using! run

def enumerationBudget (width radix : Nat) : Nat :=
  (TupleEnumerationMachine.leafBound width radix + 2 * width) * radix ^ width

noncomputable def enumerationInTime (radix : Nat) (positive : 0 < radix) :
    StateTransition.EvalsToInTime (TM2.step (program (width := width)))
      (cfg (some (enumerationLabel TupleEnumerationMachine.body)) (readyTapes radix))
      (some (cfg (some (enumerationLabel .exit)) (emittedTapes radix)))
      (enumerationBudget width radix) := by
  have run := MachineSubroutine.execution (enumerationLabel (width := width)) cleanupEntry
    TupleEnumerationMachine.program program (fun _ => rfl)
    (TupleEnumerationMachine.enumerateInTime (width := width) radix positive [] (fun _ : Unit => []))
  simpa only [MachineSubroutine.configuration, MachineSubroutine.label,
    TupleEnumerationMachine.configuration, cfg, readyTapes, emittedTapes, output,
    List.append_nil, enumerationBudget] using! run

def returnInTime (radix : Nat) :
    StateTransition.EvalsToInTime (TM2.step (program (width := width)))
      (cfg (some (enumerationLabel .exit)) (emittedTapes radix))
      (some (cfg cleanupEntry (emittedTapes radix))) 1 where
  steps := 1
  evals_in_steps := rfl
  steps_le_m := Nat.le_refl _

@[simp] theorem mem_cleanupTapes (tape : Tape width) :
    tape ∈ cleanupTapes width ↔ tape ≠ .output := by
  cases tape with
  | current i =>
      simp [cleanupTapes, source, TupleInitializationMachine.currentDestinations,
        TupleInitializationMachine.remainingDestinations, List.mem_ofFn]
  | scratch =>
      simp [cleanupTapes, source]
  | output =>
      simp [cleanupTapes, source, TupleInitializationMachine.currentDestinations,
        TupleInitializationMachine.remainingDestinations, List.mem_ofFn]
  | extra x =>
      cases x with
      | inl i =>
          simp [cleanupTapes, source, TupleInitializationMachine.currentDestinations,
        TupleInitializationMachine.remainingDestinations, List.mem_ofFn]
      | inr x =>
          cases x
          simp [cleanupTapes, source]

@[simp] theorem cleanupTapes_length :
    (cleanupTapes width).length = 2 * width + 2 := by
  simp only [cleanupTapes, List.length_append, List.length_cons, List.length_nil,
    TupleInitializationMachine.currentDestinations,
    TupleInitializationMachine.remainingDestinations, List.length_ofFn]
  omega

theorem finalTapes_cleanup (m : Nat) :
    MachineDrainMany.finalTapes (cleanupTapes width) (emittedTapes (width := width) m) =
      MachineDrainMany.haltTapes .output
        (output width m) := by
  funext tape
  rw [MachineDrainMany.finalTapes_apply]
  simp only [mem_cleanupTapes]
  by_cases htape : tape = .output
  · subst tape
    simp [MachineDrainMany.haltTapes, emittedTapes, output, TupleEnumerationMachine.tapes]
  · simp [MachineDrainMany.haltTapes, htape]

theorem cleanup_lengthSum (m : Nat) (hm : 0 < m) :
    MachineDrainMany.lengthSum (cleanupTapes width) (emittedTapes (width := width) m) =
      width * m + width := by
  have hm' : m - 1 + 1 = m := by omega
  simp [MachineDrainMany.lengthSum, cleanupTapes, source, emittedTapes,
    TupleInitializationMachine.currentDestinations, TupleInitializationMachine.remainingDestinations,
    TupleEnumerationMachine.tapes,
    List.map_ofFn, Function.comp_def, hm', Nat.add_comm]

theorem cleanup_budget (m : Nat) (hm : 0 < m) :
    MachineDrainMany.lengthSum (cleanupTapes width) (emittedTapes (width := width) m) +
      (cleanupTapes width).length = width * (m + 3) + 2 := by
  rw [cleanup_lengthSum m hm, cleanupTapes_length]
  ring

theorem cleanup_steps_le (m : Nat) (hm : 0 < m) :
    MachineDrainMany.steps (cleanupTapes width) (emittedTapes (width := width) m) ≤
      width * (m + 3) + 2 := by
  rw [← cleanup_budget m hm]
  exact MachineDrainMany.steps_le _ _

def cleanupInTime (radix : Nat) (positive : 0 < radix) :
    StateTransition.EvalsToInTime (TM2.step (program (width := width)))
      (cfg cleanupEntry (emittedTapes radix))
      (some (cfg none (MachineDrainMany.haltTapes .output (output width radix))))
      (width * (radix + 3) + 2) := by
  have run := MachineDrainMany.execution (cleanupTapes width) cleanupLabel none program
    (fun _ => rfl) (emittedTapes radix) () none
  simpa only [cfg, cleanupEntry, MachineDrainMany.finalRegister_none,
    finalTapes_cleanup, cleanup_budget radix positive] using! run

def totalBudget (width radix : Nat) : Nat :=
  ((radix + 1 + enumerationBudget width radix) + 1) + (width * (radix + 3) + 2)

noncomputable def totalInTime (radix : Nat) (positive : 0 < radix) :
    StateTransition.EvalsToInTime (TM2.step (program (width := width)))
      (cfg (some (initLabel .seed)) (inputTapes radix))
      (some (cfg none (MachineDrainMany.haltTapes .output (output width radix))))
      (totalBudget width radix) := by
  have first := StateTransition.EvalsToInTime.trans (TM2.step (program (width := width))) _ _ _ _ _
    (initializeInTime radix positive) (enumerationInTime radix positive)
  have second := StateTransition.EvalsToInTime.trans (TM2.step (program (width := width))) _ _ _ _ _
    first (returnInTime radix)
  simpa only [totalBudget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      second (cleanupInTime radix positive)

private theorem initList_eq (radix : Nat) :
    initList (machine width) (encodeWord radix) =
      cfg (some (initLabel .seed)) (inputTapes radix) := by
  unfold initList cfg
  congr 1

private theorem haltList_eq (word : List Bool) :
    haltList (machine width) word =
      cfg none (MachineDrainMany.haltTapes .output word) := by
  unfold haltList cfg
  congr 1

noncomputable def outputsInTime (radix : Nat) (positive : 0 < radix) :
    TM2OutputsInTime (machine width) (encodeWord radix) (some (output width radix))
      (totalBudget width radix) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    (initList (machine width) (encodeWord radix))
    (some (haltList (machine width) (output width radix))) (totalBudget width radix)
  rw [initList_eq, haltList_eq]
  exact totalInTime radix positive

noncomputable def time (width : Nat) : Polynomial Nat :=
  (Polynomial.X + 1) +
    ((Polynomial.C (2 * width) * (Polynomial.X + 1) + 1 + Polynomial.C (2 * width)) *
      Polynomial.X ^ width) + 1 + (Polynomial.C width * (Polynomial.X + 3) + 2)

theorem time_eval (width radix : Nat) :
    (time width).eval radix = totalBudget width radix := by
  simp [time, totalBudget, enumerationBudget, TupleEnumerationMachine.leafBound]

theorem totalBudget_mono (width : Nat) {first second : Nat} (h : first ≤ second) :
    totalBudget width first ≤ totalBudget width second := by
  have coefficient : TupleEnumerationMachine.leafBound width first + 2 * width ≤
      TupleEnumerationMachine.leafBound width second + 2 * width := by
    exact Nat.add_le_add_right
      (Nat.add_le_add_right
        (Nat.mul_le_mul_left (2 * width) (Nat.add_le_add_right h 1)) 1) (2 * width)
  have enumeration : enumerationBudget width first ≤ enumerationBudget width second :=
    Nat.mul_le_mul coefficient (Nat.pow_le_pow_left h width)
  have cleanup : width * (first + 3) + 2 ≤ width * (second + 3) + 2 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left width (Nat.add_le_add_right h 3)) 2
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right h 1) enumeration) 1) cleanup

abbrev PositiveNat := {radix : Nat // 0 < radix}

def input (radix : PositiveNat) : List Bool := encodeWord radix.val

def tuples (width : Nat) (radix : PositiveNat) : List Bool := output width radix.val

noncomputable def computation (width : Nat) :
    TM2ComputableInPolyTime input (id : List Bool → List Bool) (tuples width) where
  tm := machine width
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time width
  outputsFun radix := by
    change TM2OutputsInTime (machine width) ((input radix).map id)
      (some ((tuples width radix).map id)) ((time width).eval (input radix).length)
    have input_eq : @List.map ((machine width).Γ (machine width).k₀)
        ((machine width).Γ (machine width).k₀) id (input radix) = input radix := List.map_id _
    have output_eq : @List.map ((machine width).Γ (machine width).k₁)
        ((machine width).Γ (machine width).k₁) id (tuples width radix) = tuples width radix :=
      List.map_id _
    simp only [input_eq, output_eq]
    let run := outputsInTime (width := width) radix.val radix.property
    refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
    apply run.steps_le_m.trans
    rw [time_eval]
    exact totalBudget_mono width (by simp [input])

theorem workAlphabet_finite (width : Nat) (tape : (machine width).K) :
    Finite ((machine width).Γ tape) := by
  change Finite Bool
  infer_instance

end PerfectCompleteness.TupleIndexMachine

end OAI
