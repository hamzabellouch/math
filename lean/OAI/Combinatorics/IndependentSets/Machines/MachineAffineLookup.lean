import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineUnaryAffine
import OAI.Combinatorics.IndependentSets.Machines.MachineSubroutine

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineAffineLookup

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

end IndependentSetsGames.Foundations.Complexity.MachineAffineLookup

end OAI
