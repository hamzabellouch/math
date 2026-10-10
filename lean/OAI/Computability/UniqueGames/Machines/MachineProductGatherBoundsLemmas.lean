import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineLookupLemmas

namespace OAI

/-! Bounds on the actual work stacks left by the preserving gather. These
bounds justify clearing the query/scan remnants after each product field;
they are consequences of the exact tape formulas, not runtime assumptions. -/

namespace UniqueGamesTheorem.Explicit.MachineProductGather

open UniqueGamesTheorem.Foundations.Complexity

variable {K : Type} [DecidableEq K]

theorem affine_final_length (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (values : List Nat) (index value : Nat) (selected : values[index]? = some value)
    (base : K → List Bool) (k : K) :
    (MachineAffineLookup.finalTapes tape base values index value k).length ≤
      (base k).length + (encodeWords values).length + 1 := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  have hov := MachineLookupSpec.output_length_le values index value selected
  have hdrop : (encodeWords (values.drop (index + 1))).length ≤ (encodeWords values).length := by
    have split : encodeWords (values.take (index + 1)) ++
        encodeWords (values.drop (index + 1)) = encodeWords values := by
      rw [← encodeWords_append, List.take_append_drop]
    have h := congrArg List.length split
    simp only [List.length_append] at h
    omega
  by_cases h1 : k = tape 1
  · subst k
    simp only [MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes_index _ _ _ (hd 1 2 (by decide)) (hd 1 3 (by decide)),
      List.length_append, encodeWord_length]
    omega
  · by_cases h2 : k = tape 2
    · subst k
      simp only [MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
        MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide)), List.length_append]
      omega
    · by_cases h3 : k = tape 3
      · subst k
        rw [MachineAffineLookup.finalTapes_output, List.length_append]
        omega
      · rw [MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h1 h2 h3]
        omega

/-- One field query adds at most one table's worth of bits to any tape.
A width-fold gather therefore has a uniform linear-in-width space bound. -/
theorem finalTapes_length (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (distinct : Function.Injective placement)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (k : K) :
    (finalTapes values coefficient width placement indices offsets fields base k).length ≤
      (base k).length + width * ((encodeWords values).length + 1) := by
  induction width generalizing base with
  | zero => simp [finalTapes]
  | succ width ih =>
    let mid := MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
      (coefficient * indices 0 + offsets 0) (fields 0)
    have first := affine_final_length (placement ∘ lookupRole width)
      (distinct.comp (lookupRole_injective width)) values
      (coefficient * indices 0 + offsets 0) (fields 0) (selected 0) base k
    have rest := ih (placement ∘ shift width) (distinct.comp (shift_injective width))
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ)
      (fun i => selected i.succ) mid
    change (finalTapes values coefficient width (placement ∘ shift width)
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ) mid k).length ≤ _
    rw [Nat.add_mul, Nat.one_mul]
    dsimp only [mid] at rest
    dsimp only [mid]
    omega

end UniqueGamesTheorem.Explicit.MachineProductGather

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookupClean

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label
  | run (label : MachinePreservingLookup.Label)
  | cleanup
  deriving DecidableEq, Fintype

/-- Tape roles: 0 original table, 1 unary index, 2 working copy, 3 output,
4 copy/restore scratch. The embedded halt enters the explicit cleanup loop. -/
def statement (tape : Fin 5 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .run label => MachineSubroutine.statement (fun label => labels (.run label))
      (some (labels .cleanup)) (MachinePreservingLookup.program tape label)
  | .cleanup => MachineDrain.drain (tape 2) (labels .cleanup) exit

def program (tape : Fin 5 → K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool) :=
  statement tape id none

/-- Exact copy, lookup, return, and residual-cleanup transition count. -/
def steps (values : List Nat) (index : Nat) : Nat :=
  (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1) +
    ((encodeWords (values.drop (index + 1))).length + 1)

theorem remaining_length_le (values : List Nat) (index : Nat) :
    (encodeWords (values.drop (index + 1))).length ≤ (encodeWords values).length := by
  have h := congrArg (fun words : List Nat => (encodeWords words).length)
    (List.take_append_drop (index + 1) values)
  simp only [encodeWords_append, List.length_append] at h
  omega

theorem steps_le (values : List Nat) (index value : Nat)
    (selected : values[index]? = some value) :
    steps values index ≤ 6 * (encodeWords values).length + 4 := by
  have hc := MachinePreservingLookup.preservingLookup_steps_le values index value selected
  have hd := remaining_length_le values index
  unfold steps
  omega

noncomputable def timePolynomial : Polynomial Nat := 6 * Polynomial.X + 4

theorem steps_le_timePolynomial (values : List Nat) (index value : Nat)
    (selected : values[index]? = some value) :
    steps values index ≤ timePolynomial.eval (encodeWords values).length := by
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X] using steps_le values index value selected

/-- Actual ambient-program execution. `code` fixes the concrete instructions
at each placed label; it does not assume any execution or semantic behavior.
The frame records an empty working copy at both endpoints. -/
theorem traceAt (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps values index]
      (some ⟨some (labels (.run .copyFirst)), (ambient, register),
        MachinePreservingLookup.initialTapes tape base index indexSuffix [] output⟩) =
      some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ output)⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b :=
    fun h => hne (distinct h)
  have raw := MachinePreservingLookup.preservingLookupTrace tape distinct
    MachinePreservingLookup.Label.copyFirst MachinePreservingLookup.Label.copySecond
    MachinePreservingLookup.Label.lookup none (MachinePreservingLookup.program tape)
    rfl rfl (fun _ => rfl) base values tableWord scratchEmpty index value selected
    indexSuffix [] output ambient register
  have run := MachineSubroutine.trace (fun label => labels (.run label))
    (some (labels .cleanup)) (MachinePreservingLookup.program tape) target
    (fun label => code (.run label))
    (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1)
    _ _ raw
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at run
  have cleanup := MachineDrain.drainTrace (tape 2) (labels .cleanup) exit target
    (code .cleanup)
    (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
    (encodeWords (values.drop (index + 1))) ambient none
  have word : MachinePreservingLookup.finalTapes tape base values index value
      indexSuffix [] output (tape 2) = encodeWords (values.drop (index + 1)) := by
    simp only [MachinePreservingLookup.finalTapes,
      MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide)), List.append_nil]
  have start : Function.update
      (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
      (tape 2) (encodeWords (values.drop (index + 1))) =
      MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output := by
    rw [← word, Function.update_eq_self]
  have finish : Function.update
      (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
      (tape 2) [] = MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
        (encodeWord value ++ output) := by
    unfold MachinePreservingLookup.finalTapes MachinePreservingLookup.initialTapes
    rw [MachineLookup.update_source _ _ _ (hd 2 3 (by decide))]
  rw [start, finish] at cleanup
  rw [show steps values index =
      ((encodeWords (values.drop (index + 1))).length + 1) +
        (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1) by
        unfold steps
        omega,
    Function.iterate_add_apply, run]
  exact cleanup

/-- A timed certificate for the same actual trace, bounded by a single linear
polynomial in the original table encoding length. -/
def inTimeAt (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (.run .copyFirst)), (ambient, register),
        MachinePreservingLookup.initialTapes tape base index indexSuffix [] output⟩
      (some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ output)⟩)
      (timePolynomial.eval (encodeWords values).length) where
  steps := steps values index
  evals_in_steps := traceAt tape distinct labels exit target code base values tableWord
    scratchEmpty index value selected indexSuffix output ambient register
  steps_le_m := steps_le_timePolynomial values index value selected

/-- The framing representation is the caller's exact tape state whenever its
index and work tape contain the specified index and an empty list. -/
theorem initialTapes_eq (tape : Fin 5 → K) (base : K → List Bool)
    (index : Nat) (indexSuffix : List Bool)
    (counterWord : base (tape 1) = encodeWord index ++ indexSuffix)
    (workEmpty : base (tape 2) = []) :
    MachinePreservingLookup.initialTapes tape base index indexSuffix [] (base (tape 3)) =
      base := by
  simp only [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
    ← counterWord, ← workEmpty, Function.update_eq_self]

/-- A convenience interface starting from the caller's exact configuration. -/
theorem traceAt_fromTapes (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix : List Bool)
    (counterWord : base (tape 1) = encodeWord index ++ indexSuffix)
    (workEmpty : base (tape 2) = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps values index]
      (some ⟨some (labels (.run .copyFirst)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ base (tape 3))⟩ := by
  have h := traceAt tape distinct labels exit target code base values tableWord scratchEmpty
    index value selected indexSuffix (base (tape 3)) ambient register
  rw [initialTapes_eq tape base index indexSuffix counterWord workEmpty] at h
  exact h

/-- The complete construction has five Boolean tapes, nine control labels,
and one optional-bit register. No table data appears in its finite state. -/
def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Label
  main := .run .copyFirst
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program id

/-- The generic trace instantiates the concrete finite machine, with the same
linear bound and completely cleaned working copy. -/
def machineInTime (base : Fin 5 → List Bool) (values : List Nat)
    (tableWord : base 0 = encodeWords values) (scratchEmpty : base 4 = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some (.run .copyFirst), ((), register),
        MachinePreservingLookup.initialTapes id base index indexSuffix [] output⟩
      (some ⟨none, ((), none),
        MachinePreservingLookup.initialTapes id base 0 indexSuffix []
          (encodeWord value ++ output)⟩)
      (timePolynomial.eval (encodeWords values).length) :=
  inTimeAt id (fun _ _ h => h) id none (program id) (fun _ => rfl)
    base values tableWord scratchEmpty index value selected indexSuffix output () register

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookupClean

end OAI
