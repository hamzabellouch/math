import Mathlib.Data.List.OfFn
import OAI.Computability.UniqueGames.Machines.MachineCompare
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineControlLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev Tapes (K : Type) := K → List Bool
abbrev LocalLabel (_ : K) := Unit
abbrev Label (chosen : List K) := MachineFiniteSequence.Label (LocalLabel (K := K)) chosen
abbrev Data (K : Type) := Tapes K × Option Bool

def entry (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel (K := K)) (fun _ => ()) chosen labels exit

def localInstruction (source : K) (labels : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineDrain.drain source (labels ()) exit

def instruction (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) :
    Label chosen → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction (LocalLabel (K := K)) (fun _ => ())
    localInstruction chosen labels exit

def result (source : K) (data : Data K) : Data K :=
  (Function.update data.1 source [], none)

def cost (source : K) (data : Data K) : Nat := (data.1 source).length + 1

def finalTapes : List K → Tapes K → Tapes K
  | [], base => base
  | source :: chosen, base => finalTapes chosen (Function.update base source [])

def finalRegister : List K → Option Bool → Option Bool
  | [], register => register
  | _ :: _, _ => none

omit [DecidableEq K] in
@[simp] theorem finalRegister_none (chosen : List K) : finalRegister chosen none = none := by
  cases chosen <;> rfl

def steps : List K → Tapes K → Nat
  | [], _ => 0
  | source :: chosen, base => (base source).length + 1 +
      steps chosen (Function.update base source [])

@[simp] theorem sequence_result (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.resultOf result chosen (base, register) =
      (finalTapes chosen base, finalRegister chosen register) := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      change MachineFiniteSequence.resultOf result chosen (Function.update base source [], none) =
        (finalTapes chosen (Function.update base source []), none)
      rw [ih, finalRegister_none]

@[simp] theorem sequence_steps (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.steps result cost chosen (base, register) = steps chosen base := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      simp only [MachineFiniteSequence.steps, result, cost, steps, ih]

/-- Selected tapes are empty; every other tape word is preserved. -/
theorem finalTapes_apply (chosen : List K) (base : Tapes K) (k : K) :
    finalTapes chosen base k = if k ∈ chosen then [] else base k := by
  induction chosen generalizing base with
  | nil => simp [finalTapes]
  | cons source chosen ih =>
      rw [finalTapes, ih]
      by_cases h : k = source
      · subst k
        simp
      · simp [List.mem_cons, h]

theorem finalTapes_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∈ chosen) :
    finalTapes chosen base k = [] := by rw [finalTapes_apply, ite_eq_left h]

theorem finalTapes_not_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∉ chosen) :
    finalTapes chosen base k = base k := by rw [finalTapes_apply, ite_eq_right h]

def lengthSum (chosen : List K) (base : Tapes K) : Nat :=
  (chosen.map (fun k => (base k).length)).sum

omit [DecidableEq K] in
theorem lengthSum_mono (chosen : List K) (first second : Tapes K)
    (h : ∀ k, (first k).length ≤ (second k).length) :
    lengthSum chosen first ≤ lengthSum chosen second := by
  induction chosen with
  | nil => exact Nat.le_refl 0
  | cons source chosen ih =>
      simp only [lengthSum, List.map_cons, List.sum_cons] at ih ⊢
      exact Nat.add_le_add (h source) ih

/-- This upper bound remains valid when the cleanup list repeats tapes. -/
theorem steps_le (chosen : List K) (base : Tapes K) :
    steps chosen base ≤ lengthSum chosen base + chosen.length := by
  induction chosen generalizing base with
  | nil => simp [steps, lengthSum]
  | cons source chosen ih =>
      have hshort : ∀ k, ((Function.update base source []) k).length ≤ (base k).length := by
        intro k
        by_cases h : k = source
        · subst k
          simp
        · simp [Function.update_of_ne h]
      have hsum := lengthSum_mono chosen (Function.update base source []) base hshort
      have htail := ih (Function.update base source [])
      simp only [steps, lengthSum, List.map_cons, List.sum_cons, List.length_cons] at hsum htail ⊢
      omega

theorem steps_le_uniform (chosen : List K) (base : Tapes K) (bound : Nat)
    (h : ∀ k, (base k).length ≤ bound) :
    steps chosen base ≤ chosen.length * (bound + 1) := by
  have hsum : lengthSum chosen base ≤ chosen.length * bound := by
    induction chosen with
    | nil => simp [lengthSum]
    | cons source chosen ih =>
        simp only [lengthSum, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
          Nat.one_mul] at ih ⊢
        have hs := h source
        omega
  have hc := steps_le chosen base
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Exact execution of all concrete drains in the supplied ambient program. -/
theorem trace (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps chosen base]
      (some ⟨entry chosen labels exit, (ambient, register), base⟩) =
    some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩ := by
  have run := MachineFiniteSequence.trace
    (LocalLabel := LocalLabel (K := K)) (main := fun _ => ())
    (localInstruction := localInstruction (σ := σ)) (result := result) (cost := cost)
    program (fun _ : Data K => True) (fun data => (ambient, data.2)) (fun data => data.1)
    chosen (by intros; trivial)
    (by
      intro source _ localLabels localExit atLocal data _
      rcases data with ⟨tapes, reg⟩
      simpa only [cost, result, Function.update_eq_self] using
        MachineDrain.drainTrace source (localLabels ()) localExit program (atLocal ())
          tapes (tapes source) ambient reg)
    labels exit atLabels (base, register) trivial
  simpa only [sequence_steps, sequence_result, entry] using run

def execution (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry chosen labels exit, (ambient, register), base⟩
      (some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩)
      (lengthSum chosen base + chosen.length) where
  steps := steps chosen base
  evals_in_steps := trace chosen labels exit program atLabels base ambient register
  steps_le_m := steps_le chosen base

/-- An executable complete cleanup list from an explicit finite enumeration. -/
def workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K) : List K :=
  (List.ofFn (fun i => enumeration i)).filter (fun k => decide (k ≠ output))

@[simp] theorem mem_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output k : K) :
    k ∈ workTapes enumeration output ↔ k ≠ output := by
  have hmem : k ∈ List.ofFn (fun i => enumeration i) := by
    apply List.mem_ofFn.mpr
    exact ⟨enumeration.symm k, enumeration.apply_symm_apply k⟩
  simp [workTapes, hmem]

theorem workTapes_length_le {N : Nat} (enumeration : Fin N ≃ K) (output : K) :
    (workTapes enumeration output).length ≤ N := by
  simpa only [workTapes, List.length_ofFn] using
    List.length_filter_le (fun k => decide (k ≠ output)) (List.ofFn (fun i => enumeration i))

/-- The tape component of the actual halted configuration: only output remains. -/
def haltTapes (output : K) (word : List Bool) : Tapes K :=
  fun k => if k = output then word else []

theorem finalTapes_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (base : Tapes K) :
    finalTapes (workTapes enumeration output) base = haltTapes output (base output) := by
  funext k
  rw [finalTapes_apply]
  by_cases h : k = output
  · subst k
    simp [haltTapes]
  · simp [haltTapes, h]

/-- With a clean register, complete work-tape cleanup reaches the standard
halted shape, preserving the output word and the ambient state exactly. -/
theorem cleanupTrace {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (labels : Label (workTapes enumeration output) → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) =
      instruction (workTapes enumeration output) labels none l)
    (base : Tapes K) (ambient : σ) :
    (advance (TM2.step program))^[steps (workTapes enumeration output) base]
      (some ⟨entry (workTapes enumeration output) labels none, (ambient, none), base⟩) =
    some ⟨none, (ambient, none), haltTapes output (base output)⟩ := by
  simpa only [finalRegister_none, finalTapes_workTapes] using
    trace (workTapes enumeration output) labels none program atLabels base ambient none

end UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFieldProfile

open Turing

abbrev Profile (q : Nat) := Fin q → Fin q → Bool

def equalityProfile {q : Nat} (words : Fin q → List Bool) : Profile q :=
  fun i j => decide (words i = words j)

theorem equalityProfile_encodeWord {q : Nat} (names : Fin q → Nat) (i j : Fin q) :
    equalityProfile (fun k => encodeWord (names k)) i j = decide (names i = names j) := by
  have h : encodeWord (names i) = encodeWord (names j) ↔ names i = names j := by
    constructor
    · intro heq
      have hh := congrArg List.length heq
      simpa only [encodeWord_length, Nat.add_right_cancel_iff] using hh
    · rintro heq
      rw [heq]
  simp only [equalityProfile, h]

section Transport
variable {K Λ σ τ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem statement_roundtrip (e : σ ≃ τ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ τ) :
    MachineControl.statement id e (MachineControl.statement id e.symm q) = q := by
  induction q <;> simp_all [MachineControl.statement]

def copyStateEquiv (σ : Type) :
    ((σ × Bool × Option Bool) × Option Bool) ≃ MachineCompare.State σ where
  toFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  invFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def normalState (ambient : σ) : MachineCompare.State σ := (ambient, false, none, none)

def copyStatement (q : TM2.Stmt (fun _ : K => Bool) Λ
    ((σ × Bool × Option Bool) × Option Bool)) :
    TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ) :=
  MachineControl.statement id (copyStateEquiv σ) q

def copyInCompareState (source destination scratch : K)
    (hSD : source ≠ destination) (hST : source ≠ scratch) (hDT : destination ≠ scratch)
    (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atFirst : program firstLabel = copyStatement
      (Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel)))
    (atSecond : program secondLabel = copyStatement
      (MachineCopy.forkLoop scratch source destination false secondLabel exit))
    (base : K → List Bool) (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, normalState ambient, base⟩
      (some ⟨exit, normalState ambient,
        Function.update base destination (base source ++ base destination)⟩)
      (2 * ((base source).length + 1)) := by
  let e := copyStateEquiv σ
  let view := MachineControl.program (Equiv.refl Λ) e.symm program
  have hfirst : view firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel) := by
    dsimp [view, MachineControl.program]
    rw [atFirst]
    exact statement_roundtrip e.symm _
  have hsecond : view secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel exit := by
    dsimp [view, MachineControl.program]
    rw [atSecond]
    exact statement_roundtrip e.symm _
  let run := MachineCopy.copyInTime source destination scratch hSD hST hDT false
    firstLabel secondLabel exit view hfirst hsecond base hScratch (ambient, false, none) none
  have hprogram : MachineControl.program (Equiv.refl Λ) e view = program := by
    funext label
    exact statement_roundtrip e (program label)
  have hsim (a b : TM2.Cfg (fun _ : K => Bool) Λ ((σ × Bool × Option Bool) × Option Bool))
      (hab : TM2.step view a = some b) :
      TM2.step program (MachineControl.configuration id e a) =
        some (MachineControl.configuration id e b) := by
    have hh := MachineControl.step_simulation (Equiv.refl Λ) e view a
    rw [hprogram, hab] at hh
    exact hh
  have lifted := MachineComposition.liftExecutionInTime (TM2.step view) (TM2.step program)
    (MachineControl.configuration id e) hsim run
  simpa [MachineControl.configuration, copyStateEquiv, normalState, e] using lifted

end Transport

section PreservedComparison
variable {K Λ σ : Type} [DecidableEq K]

def nonDestructiveCompareInTime (left right workLeft workRight scratch : K)
    (hleft : left ≠ workLeft ∧ left ≠ workRight ∧ left ≠ scratch)
    (hright : right ≠ workLeft ∧ right ≠ workRight ∧ right ≠ scratch)
    (hwork : workLeft ≠ workRight ∧ workLeft ≠ scratch ∧ workRight ≠ scratch)
    (leftFirst leftSecond rightFirst rightSecond compareLabel : Λ)
    (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atLeftFirst : program leftFirst = copyStatement
      (Reduction.MachineTransfer.loopAt left scratch id false leftFirst (some leftSecond)))
    (atLeftSecond : program leftSecond = copyStatement
      (MachineCopy.forkLoop scratch left workLeft false leftSecond (some rightFirst)))
    (atRightFirst : program rightFirst = copyStatement
      (Reduction.MachineTransfer.loopAt right scratch id false rightFirst (some rightSecond)))
    (atRightSecond : program rightSecond = copyStatement
      (MachineCopy.forkLoop scratch right workRight false rightSecond (some compareLabel)))
    (atCompare : program compareLabel =
      MachineCompare.loop workLeft workRight compareLabel equalExit differentExit)
    (base : K → List Bool) (hWL : base workLeft = []) (hWR : base workRight = [])
    (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some leftFirst, normalState ambient, base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        normalState ambient, base⟩)
      (2 * ((base left).length + 1) + 2 * ((base right).length + 1) +
        max (base left).length (base right).length + 1) := by
  let t₁ := Function.update base workLeft (base left)
  let t₂ := Function.update t₁ workRight (base right)
  have h₁ := copyInCompareState left workLeft scratch hleft.1 hleft.2.2 hwork.2.1
    leftFirst leftSecond (some rightFirst) program atLeftFirst atLeftSecond base hScratch ambient
  simp only [hWL, List.append_nil] at h₁
  have hSR : t₁ right = base right := by simp [t₁, hright.1]
  have hDR : t₁ workRight = [] := by simp [t₁, Ne.symm hwork.1, hWR]
  have hTR : t₁ scratch = [] := by simp [t₁, Ne.symm hwork.2.1, hScratch]
  have h₂ := copyInCompareState right workRight scratch hright.2.1 hright.2.2 hwork.2.2
    rightFirst rightSecond (some compareLabel) program atRightFirst atRightSecond t₁ hTR ambient
  rw [hSR, hDR] at h₂
  simp only [List.append_nil] at h₂
  have hL : t₂ workLeft = base left := by simp [t₂, t₁, hwork.1]
  have hR : t₂ workRight = base right := by simp [t₂]
  have hrestore : Reduction.MachineTransfer.tapesAt workLeft workRight t₂ [] [] = base := by
    funext p
    by_cases hl : p = workLeft
    · subst p
      simp [Reduction.MachineTransfer.tapesAt, hwork.1, hWL]
    · by_cases hr : p = workRight
      · subst p
        simp [Reduction.MachineTransfer.tapesAt, hWR]
      · simp [Reduction.MachineTransfer.tapesAt, t₂, t₁, hl, hr]
  have h₃ := MachineCompare.compareInTime workLeft workRight hwork.1 compareLabel
    equalExit differentExit program atCompare t₂ ambient none none
  rw [hL, hR, hrestore] at h₃
  let h₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁ h₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁₂ h₃
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

end PreservedComparison

def setEntry {q : Nat} (profile : Profile q) (pair : Fin q × Fin q) (bit : Bool) : Profile q :=
  Function.update profile pair.1 (Function.update (profile pair.1) pair.2 bit)

theorem setEntry_apply {q : Nat} (profile : Profile q) (pair : Fin q × Fin q)
    (bit : Bool) (i j : Fin q) :
    setEntry profile pair bit i j = if (i, j) = pair then bit else profile i j := by
  rcases pair with ⟨a, b⟩
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [setEntry, hi, hj]

def setExpected {q : Nat} (words : Fin q → List Bool) (profile : Profile q)
    (pair : Fin q × Fin q) : Profile q :=
  setEntry profile pair (equalityProfile words pair.1 pair.2)

def foldProfile {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) : Profile q := cells.foldl (setExpected words) initial

theorem foldProfile_apply {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (i j : Fin q) :
    foldProfile words initial cells i j =
      if (i, j) ∈ cells then equalityProfile words i j else initial i j := by
  induction cells generalizing initial with
  | nil => rfl
  | cons pair rest ih =>
    change foldProfile words (setExpected words initial pair) rest i j = _
    rw [ih]
    by_cases hrest : (i, j) ∈ rest
    · simp [hrest]
    · by_cases hpair : (i, j) = pair
      · subst pair
        simp [hrest, setExpected, setEntry_apply]
      · simp [hrest, hpair, setExpected, setEntry_apply]

abbrev Tape (q : Nat) := Fin q ⊕ Fin 3
abbrev Label {q : Nat} (cells : List (Fin q × Fin q)) := Fin (cells.length + 1) × Fin 7

def labelAt {q : Nat} (cells : List (Fin q × Fin q)) (r : Nat) (phase : Fin 7) : Label cells :=
  (⟨min r cells.length, by omega⟩, phase)

def storePair {q : Nat} (pair : Fin q × Fin q) (bit : Bool)
    {Λ : Type} (nextLabel : Λ) :
    TM2.Stmt (fun _ : Tape q => Bool) Λ (MachineCompare.State (Profile q)) :=
  .load (fun state => normalState (setEntry state.1 pair bit)) (.goto fun _ => nextLabel)

/-- The fixed list of pairs determines all control labels and original fields.
The program compares only copied work-stack heads, then stores one finite bit. -/
def profileProgram {q : Nat} (cells : List (Fin q × Fin q)) (label : Label cells) :
    TM2.Stmt (fun _ : Tape q => Bool) (Label cells) (MachineCompare.State (Profile q)) :=
  if h : label.1.val < cells.length then
    let pair := cells[label.1.val]
    let r := label.1.val
    match label.2.val with
    | 0 => copyStatement (Reduction.MachineTransfer.loopAt (.inl pair.1) (.inr 2) id false
        (labelAt cells r 0) (some (labelAt cells r 1)))
    | 1 => copyStatement (MachineCopy.forkLoop (.inr 2) (.inl pair.1) (.inr 0) false
        (labelAt cells r 1) (some (labelAt cells r 2)))
    | 2 => copyStatement (Reduction.MachineTransfer.loopAt (.inl pair.2) (.inr 2) id false
        (labelAt cells r 2) (some (labelAt cells r 3)))
    | 3 => copyStatement (MachineCopy.forkLoop (.inr 2) (.inl pair.2) (.inr 1) false
        (labelAt cells r 3) (some (labelAt cells r 4)))
    | 4 => MachineCompare.loop (.inr 0) (.inr 1) (labelAt cells r 4)
        (some (labelAt cells r 5)) (some (labelAt cells r 6))
    | 5 => storePair pair true (labelAt cells (r + 1) 0)
    | _ => storePair pair false (labelAt cells (r + 1) 0)
  else .halt

def pairTime {q : Nat} (words : Fin q → List Bool) (pair : Fin q × Fin q) : Nat :=
  2 * ((words pair.1).length + 1) + 2 * ((words pair.2).length + 1) +
    max (words pair.1).length (words pair.2).length + 2

def prefixProfile {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (r : Nat) : Profile q :=
  foldProfile words initial (cells.take r)

def prefixTime {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) : Nat :=
  ((cells.take r).map (pairTime words)).sum

theorem prefixProfile_succ {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length) :
    prefixProfile words initial cells (r + 1) =
      setExpected words (prefixProfile words initial cells r) cells[r] := by
  unfold prefixProfile foldProfile
  rw [List.take_succ_eq_append_getElem hr, List.foldl_append]
  rfl

theorem prefixTime_succ {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length) :
    prefixTime words cells (r + 1) = prefixTime words cells r + pairTime words cells[r] := by
  unfold prefixTime
  rw [List.take_succ_eq_append_getElem hr, List.map_append, List.sum_append]
  rfl

/-- One fully constructed copy/copy/compare/store stage, restoring every stack. -/
def stageInTime {q : Nat} (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length)
    (base : Tape q → List Bool) (hwork : ∀ w : Fin 3, base (.inr w) = []) (profile : Profile q) :
    StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells r 0), normalState profile, base⟩
      (some ⟨some (labelAt cells (r + 1) 0),
        normalState (setExpected (fun i => base (.inl i)) profile cells[r]), base⟩)
      (pairTime (fun i => base (.inl i)) cells[r]) := by
  let pair := cells[r]
  have copied := nonDestructiveCompareInTime (.inl pair.1) (.inl pair.2)
    (.inr 0 : Tape q) (.inr 1) (.inr 2) (by simp) (by simp) (by simp)
    (labelAt cells r 0) (labelAt cells r 1) (labelAt cells r 2) (labelAt cells r 3)
    (labelAt cells r 4) (some (labelAt cells r 5)) (some (labelAt cells r 6))
    (profileProgram cells)
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr])
    base (hwork 0) (hwork 1) (hwork 2) profile
  have stored : StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨if base (.inl pair.1) = base (.inl pair.2) then some (labelAt cells r 5)
        else some (labelAt cells r 6), normalState profile, base⟩
      (some ⟨some (labelAt cells (r + 1) 0),
        normalState (setExpected (fun i => base (.inl i)) profile pair), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step (profileProgram cells)
        ⟨if base (.inl pair.1) = base (.inl pair.2) then some (labelAt cells r 5)
          else some (labelAt cells r 6), normalState profile, base⟩ = _
      by_cases heq : base (.inl pair.1) = base (.inl pair.2)
      · simp [heq, TM2.step, profileProgram, labelAt,
          Nat.min_eq_left hr.le, hr, storePair, TM2.stepAux, normalState,
          setExpected, equalityProfile, pair]
      · simp [heq, TM2.step, profileProgram, labelAt,
          Nat.min_eq_left hr.le, hr, storePair, TM2.stepAux, normalState,
          setExpected, equalityProfile, pair]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copied stored
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  dsimp only [pair] at h
  dsimp only [pairTime]
  omega

/-- Compose the actual stages up to any fixed position in the pair list. -/
def prefixInTime {q : Nat} (cells : List (Fin q × Fin q))
    (base : Tape q → List Bool) (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q)
    (r : Nat) (hr : r ≤ cells.length) :
    StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells 0 0), normalState initial, base⟩
      (some ⟨some (labelAt cells r 0),
        normalState (prefixProfile (fun i => base (.inl i)) initial cells r), base⟩)
      (prefixTime (fun i => base (.inl i)) cells r) := by
  induction r with
  | zero =>
    exact { steps := 0, evals_in_steps := rfl, steps_le_m := Nat.le_refl _ }
  | succ r ih =>
    have hrl : r < cells.length := by omega
    let first := ih (by omega)
    let second := stageInTime cells r hrl base hwork
      (prefixProfile (fun i => base (.inl i)) initial cells r)
    let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
    rw [prefixProfile_succ _ _ _ _ hrl, prefixTime_succ _ _ _ hrl]
    exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

def allPairs (q : Nat) : List (Fin q × Fin q) :=
  (List.finRange q).flatMap fun i => (List.finRange q).map fun j => (i, j)

theorem mem_allPairs {q : Nat} (i j : Fin q) : (i, j) ∈ allPairs q := by
  simp [allPairs]

theorem length_allPairs (q : Nat) : (allPairs q).length = q * q := by
  simp [allPairs, List.length_flatMap]

theorem foldProfile_allPairs {q : Nat} (words : Fin q → List Bool) (initial : Profile q) :
    foldProfile words initial (allPairs q) = equalityProfile words := by
  funext i j
  simp [foldProfile_apply, mem_allPairs]

/-- A concrete finite machine for the full field equality matrix. -/
def profileMachine (q : Nat) : FinTM2 where
  K := Tape q
  k₀ := .inr 0
  k₁ := .inr 0
  Γ _ := Bool
  Λ := Label (allPairs q)
  main := labelAt (allPairs q) 0 0
  σ := MachineCompare.State (Profile q)
  initialState := normalState (fun _ _ => false)
  m := profileProgram (allPairs q)

/-- Compute every matrix entry while preserving all original field stacks. -/
def profileInTime (q : Nat) (base : Tape q → List Bool)
    (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q) :
    StateTransition.EvalsToInTime (profileMachine q).step
      ⟨some (labelAt (allPairs q) 0 0), normalState initial, base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩)
      (((allPairs q).map (pairTime (fun i => base (.inl i)))).sum + 1) := by
  let cells := allPairs q
  have first := prefixInTime cells base hwork initial cells.length (Nat.le_refl _)
  have last : StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells cells.length 0),
        normalState (prefixProfile (fun i => base (.inl i)) initial cells cells.length), base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step (profileProgram cells)
        ⟨some (labelAt cells cells.length 0),
          normalState (prefixProfile (fun i => base (.inl i)) initial cells cells.length), base⟩ = _
      simp [TM2.step, profileProgram, labelAt, TM2.stepAux,
        prefixProfile, cells, foldProfile_allPairs]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  simpa [prefixTime, cells, Nat.add_comm] using h

theorem pairTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (pair : Fin q × Fin q) :
    pairTime words pair ≤ 5 * L + 6 := by
  have hi := hL pair.1
  have hj := hL pair.2
  have hm := max_le hi hj
  dsimp only [pairTime]
  omega

theorem totalTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (cells : List (Fin q × Fin q)) :
    (cells.map (pairTime words)).sum ≤ cells.length * (5 * L + 6) := by
  induction cells with
  | nil => simp
  | cons pair rest ih =>
    have hp := pairTime_le words L hL pair
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A linear bound in the maximum original field length, for fixed `q`.
The actual machine and execution witness are retained. -/
def profileInTime_bounded (q : Nat) (base : Tape q → List Bool)
    (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q)
    (L : Nat) (hL : ∀ i, (base (.inl i)).length ≤ L) :
    StateTransition.EvalsToInTime (profileMachine q).step
      ⟨some (labelAt (allPairs q) 0 0), normalState initial, base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩)
      (q * q * (5 * L + 6) + 1) := by
  let run := profileInTime q base hwork initial
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  apply run.steps_le_m.trans
  apply Nat.add_le_add_right
  simpa only [length_allPairs] using totalTime_le (fun i => base (.inl i)) L hL (allPairs q)

end UniqueGamesTheorem.Foundations.Complexity.MachineFieldProfile

end OAI
