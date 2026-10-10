import Mathlib
import OAI.Computability.MinUncut.Machines.MachineFiniteAlphabet

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def initialTapes (tape : Fin 5 → K) (base : K → List Bool)
    (index : Nat) (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord index ++ indexSuffix) workSuffix output

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat)
    (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord 0 ++ indexSuffix)
    (encodeWords (values.drop (index + 1)) ++ workSuffix) (encodeWord value ++ output)

theorem lookupFramedHaltTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (MachineLookup.program index source destination)))^[
      MachineLookupSpec.steps values i + 1]
      (some ⟨some MachineLookup.Label.guard, (ambient,register),
        MachineLookup.tapes index source destination base (encodeWord i ++ indexSuffix)
          (encodeWords values ++ suffix) output⟩) =
      some ⟨none, (ambient,none), MachineLookup.tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  rw [Function.iterate_succ_apply',
    MachineLookup.lookupTrace_some index source destination his hid hsd
      base values i value selected indexSuffix suffix output ambient register]
  simp only [advance_some, TM2.step, MachineLookup.program, TM2.stepAux]

theorem preservingLookupTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (firstLabel secondLabel : Λ) (lookupLabels : MachineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 4) id false firstLabel (some secondLabel))
    (atSecond : program secondLabel = MachineCopy.forkLoop
      (tape 4) (tape 0) (tape 2) false secondLabel (some (lookupLabels .guard)))
    (atLookup : ∀ l, program (lookupLabels l) =
      MachineSubroutine.statement lookupLabels exit (MachineLookup.program (tape 1) (tape 2) (tape 3) l))
    (base : K → List Bool) (values : List Nat) (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = []) (i value : Nat) (selected : values[i]? = some value)
    (indexSuffix workSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
      2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1]
      (some ⟨some firstLabel, (ambient,register),
        initialTapes tape base i indexSuffix workSuffix output⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values i value indexSuffix workSuffix output⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  let start := initialTapes tape base i indexSuffix workSuffix output
  have htable : start (tape 0) = encodeWords values := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 0 3 (by decide))] using tableWord
  have hs : start (tape 4) = [] := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 4 1 (by decide)) (hd 4 2 (by decide)) (hd 4 3 (by decide))] using scratchEmpty
  have hwork : start (tape 2) = workSuffix := by
    simp only [start, initialTapes, MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide))]
  have hcopy := MachineCopy.copyTrace (tape 0) (tape 2) (tape 4)
    (hd 0 2 (by decide)) (hd 0 4 (by decide)) (hd 2 4 (by decide)) false
    firstLabel secondLabel (some (lookupLabels .guard)) program atFirst atSecond start hs ambient register
  rw [htable, hwork] at hcopy
  simp only [start, initialTapes, MachineLookup.update_source _ _ _ (hd 2 3 (by decide))] at hcopy
  have hlookup := MachineSubroutine.trace lookupLabels exit
    (MachineLookup.program (tape 1) (tape 2) (tape 3)) program atLookup
    (MachineLookupSpec.steps values i + 1) _ _
    (lookupFramedHaltTrace_some (tape 1) (tape 2) (tape 3)
      (hd 1 2 (by decide)) (hd 1 3 (by decide)) (hd 2 3 (by decide))
      base values i value selected indexSuffix workSuffix output ambient none)
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at hlookup
  rw [show 2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 =
      (MachineLookupSpec.steps values i + 1) + 2 * ((encodeWords values).length + 1) by omega,
    Function.iterate_add_apply]
  change (advance (TM2.step program))^[MachineLookupSpec.steps values i + 1]
    ((advance (TM2.step program))^[2 * ((encodeWords values).length + 1)]
      (some ⟨some firstLabel, (ambient,register),
        MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
          (encodeWord i ++ indexSuffix) workSuffix output⟩)) = _
  rw [hcopy]
  exact hlookup

theorem preservingLookup_steps_le (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) :
    2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 ≤
      5 * (encodeWords values).length + 3 := by
  have ht := MachineLookupSpec.steps_le_input_encoding_size values i
  have hi := MachineLookupSpec.index_length_le values i value selected
  omega

def preservingLookupInTime (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (firstLabel secondLabel : Λ) (lookupLabels : MachineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 4) id false firstLabel (some secondLabel))
    (atSecond : program secondLabel = MachineCopy.forkLoop
      (tape 4) (tape 0) (tape 2) false secondLabel (some (lookupLabels .guard)))
    (atLookup : ∀ l, program (lookupLabels l) =
      MachineSubroutine.statement lookupLabels exit (MachineLookup.program (tape 1) (tape 2) (tape 3) l))
    (base : K → List Bool) (values : List Nat) (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = []) (i value : Nat) (selected : values[i]? = some value)
    (indexSuffix workSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient,register), initialTapes tape base i indexSuffix workSuffix output⟩
      (some ⟨exit, (ambient,none), finalTapes tape base values i value indexSuffix workSuffix output⟩)
      (5 * (encodeWords values).length + 3) where
  steps := 2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1
  evals_in_steps := preservingLookupTrace tape distinct firstLabel secondLabel lookupLabels exit
    program atFirst atSecond atLookup base values tableWord scratchEmpty i value selected
    indexSuffix workSuffix output ambient register
  steps_le_m := preservingLookup_steps_le values i value selected

inductive Label
  | copyFirst | copySecond | lookup (l : MachineLookup.Label)
  deriving DecidableEq, Fintype

def program (tape : Fin 5 → K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false .copySecond (some (.lookup .guard))
  | .lookup l => MachineSubroutine.statement Label.lookup none
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Label
  main := .copyFirst
  σ := Unit × Option Bool
  initialState := ((),none)
  m := program id

end MinUncutGames.Foundations.Complexity.MachinePreservingLookup

namespace MinUncutGames.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label
  | seed | scan | restore | copyFirst | copySecond
  | lookup (l : MachineLookup.Label)
  deriving DecidableEq, Fintype

def instruction (source : K) (tape : Fin 5 → K) (coefficient offset : Nat)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed (tape 1) offset (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source (tape 4) (tape 1)
      coefficient (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt (tape 4) source id false
      (labels .restore) (some (labels .copyFirst))
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false
      (labels .copyFirst) (some (labels .copySecond))
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false
      (labels .copySecond) (some (labels (.lookup .guard)))
  | .lookup l => MachineSubroutine.statement (fun q => labels (.lookup q)) exit
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

def steps (values : List Nat) (a coefficient offset : Nat) : Nat :=
  (2 * (a + 1) + 1) +
    (2 * ((encodeWords values).length + 1) +
      MachineLookupSpec.steps values (coefficient * a + offset) + 1)

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) : K → List Bool :=
  MachinePreservingLookup.finalTapes tape base values index value
    (base (tape 1)) (base (tape 2)) (base (tape 3))

theorem initialTapes_eq_update (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (i : Nat) :
    MachinePreservingLookup.initialTapes tape base i
      (base (tape 1)) (base (tape 2)) (base (tape 3)) =
      Function.update base (tape 1) (encodeWord i ++ base (tape 1)) := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  funext k
  by_cases h₁ : k = tape 1
  · subst k
    simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
      hd 1 2 (by decide), hd 1 3 (by decide)]
  · by_cases h₂ : k = tape 2
    · subst k
      simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁,
        hd 2 3 (by decide)]
    · by_cases h₃ : k = tape 3
      · subst k
        simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁]
      · simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁, h₂, h₃]

theorem affineLookupTrace (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ i, source ≠ tape i)
    (coefficient offset : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction source tape coefficient offset labels exit l)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values) (scratchEmpty : base (tape 4) = [])
    (a : Nat) (suffix : List Bool) (sourceWord : base source = encodeWord a ++ suffix)
    (value : Nat) (selected : values[coefficient * a + offset]? = some value)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values a coefficient offset]
      (some ⟨some (labels .seed), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values (coefficient * a + offset) value⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have haffine := MachineUnaryAffineAt.seededAffineTrace source (tape 4) (tape 1)
    (outside 4) (outside 1) (hd 4 1 (by decide)) coefficient offset
    (labels .seed) (labels .scan) (labels .restore) (some (labels .copyFirst))
    program (atLabels .seed) (atLabels .scan) (atLabels .restore)
    base a suffix sourceWord scratchEmpty ambient register
  have hlookup := MachinePreservingLookup.preservingLookupTrace tape distinct
    (labels .copyFirst) (labels .copySecond) (fun q => labels (.lookup q)) exit
    program (atLabels .copyFirst) (atLabels .copySecond) (fun q => atLabels (.lookup q))
    base values tableWord scratchEmpty (coefficient * a + offset) value selected
    (base (tape 1)) (base (tape 2)) (base (tape 3)) ambient none
  rw [initialTapes_eq_update tape distinct] at hlookup
  rw [steps, Nat.add_comm, Function.iterate_add_apply, haffine]
  exact hlookup

theorem steps_le (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value) :
    steps values a coefficient offset ≤ 2 * a + 5 * (encodeWords values).length + 6 := by
  have h := MachinePreservingLookup.preservingLookup_steps_le values
    (coefficient * a + offset) value selected
  unfold steps
  omega

theorem steps_le_table (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value)
    (ha : a ≤ (encodeWords values).length) :
    steps values a coefficient offset ≤ 7 * (encodeWords values).length + 6 := by
  have h := steps_le values a coefficient offset value selected
  omega

theorem finalTapes_other (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) (k : K)
    (h₁ : k ≠ tape 1) (h₂ : k ≠ tape 2) (h₃ : k ≠ tape 3) :
    finalTapes tape base values index value k = base k :=
  MachineLookup.tapes_other _ _ _ _ h₁ h₂ h₃ _ _ _ _

theorem finalTapes_output (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) :
    finalTapes tape base values index value (tape 3) = encodeWord value ++ base (tape 3) :=
  MachineLookup.tapes_destination _ _ _ _ _ _ _

def machine (coefficient offset : Nat) : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label
  main := .seed
  σ := Unit × Option Bool
  initialState := ((),none)
  m := instruction 0 Fin.succ coefficient offset id none

end MinUncutGames.Foundations.Complexity.MachineAffineLookup

end OAI
