import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.MachineFieldTemplate

namespace OAI

/-!
A fixed number of copies of an arbitrary bit stream, by a real finite-alphabet
machine. This is the uniform-rounding stream primitive: copying a header-free
occurrence stream `C` times gives multiplicity `C` to every listed occurrence.
The input is preserved during the copy phase, physically drained, and replaced
by the forward-order result. No unbounded word is stored in finite control.
-/

namespace UniqueGamesTheorem.Explicit.MachineFixedCopies

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction

def copies (C : Nat) (word : List Bool) : List Bool :=
  (List.replicate C word).flatten

@[simp] theorem copies_zero (word : List Bool) : copies 0 word = [] := rfl

@[simp] theorem copies_succ (C : Nat) (word : List Bool) :
    copies (C + 1) word = word ++ copies C word := by
  simp [copies, List.replicate_succ]

@[simp] theorem copies_length (C : Nat) (word : List Bool) :
    (copies C word).length = C * word.length := by
  induction C with
  | zero => simp
  | succ C ih => simp [ih, Nat.add_mul, Nat.add_comm]

def tokens (C : Nat) : List (MachineFieldTemplate.Token 1) :=
  List.replicate C (.copy 0)

@[simp] theorem tokens_length (C : Nat) : (tokens C).length = C := by simp [tokens]

@[simp] theorem templateOutput (C : Nat) (word : List Bool) :
    MachineFieldTemplate.templateOutput (tokens C) (fun _ => word) = copies C word := by
  induction C with
  | zero => rfl
  | succ C ih =>
    simp only [tokens, List.replicate_succ, MachineFieldTemplate.templateOutput,
      List.flatMap_cons, MachineFieldTemplate.tokenOutput, copies_succ] at *
    rw [ih]

@[simp] theorem copiedLength (C : Nat) (word : List Bool) :
    MachineFieldTemplate.copiedLength (tokens C) (fun _ => word) = C * word.length := by
  simp [MachineFieldTemplate.copiedLength, tokens]

abbrev Tape := Fin 3
abbrev Label (C : Nat) := MachineFieldTemplate.Label (tokens C).length ⊕ Bool
abbrev State := MachineFieldTemplate.State Unit

def initialState : State := (((), ()), none)

def program (C : Nat) : Label C → TM2.Stmt (fun _ : Tape => Bool) (Label C) State
  | .inl label => MachineFieldTemplate.instruction (tokens C) (fun _ => 0) 1 2
      Sum.inl (some (.inr false)) label
  | .inr false => MachineDrain.drain 0 (.inr false) (some (.inr true))
  | .inr true => MachineTransfer.loopAt 2 0 id false (.inr true) none

def machine (C : Nat) : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Label C
  main := .inl (MachineFieldTemplate.startAt (tokens C).length 0)
  σ := State
  initialState := initialState
  m := program C

def tapes (input accumulator : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 2 then accumulator else []

theorem initList_eq (C : Nat) (word : List Bool) :
    initList (machine C) word =
      ⟨some (.inl (MachineFieldTemplate.startAt (tokens C).length 0)),
        initialState, tapes word []⟩ := by
  unfold initList
  congr 1
  funext k
  change Tape at k
  (fin_cases k <;> simp [machine, tapes]); rfl

theorem haltList_eq (C : Nat) (word : List Bool) :
    haltList (machine C) word = ⟨none, initialState, tapes word []⟩ := by
  unfold haltList
  congr 1
  funext k
  change Tape at k
  (fin_cases k <;> simp [machine, tapes]); rfl

theorem copied_tapes (C : Nat) (word : List Bool) :
    MachineFieldTemplate.outputTapes (tapes word []) 2 (copies C word) =
      tapes word (copies C word).reverse := by
  funext k
  fin_cases k <;> simp [MachineFieldTemplate.outputTapes, tapes]

theorem drained_tapes (word accumulator : List Bool) :
    Function.update (tapes word accumulator) 0 [] = tapes [] accumulator := by
  funext k
  fin_cases k <;> simp [tapes]

theorem transferred_tapes (word : List Bool) :
    MachineTransfer.tapesAt (2 : Tape) 0 (tapes [] word.reverse) []
        word = tapes word [] := by
  funext k
  fin_cases k <;> simp [MachineTransfer.tapesAt, tapes]

/-- Copy, cleanup, and reversal all run on the actual finite transition program. -/
def outputInTime (C : Nat) (word : List Bool) :
    TM2OutputsInTime (machine C) word (some (copies C word))
      ((4 * C + 1) * word.length + 3 * C + 3) := by
  have copy := MachineFieldTemplate.phaseInTime (tokens C) (fun _ : Fin 1 => (0 : Tape))
    1 2 (by intro j; decide) (by intro j; decide) (by decide)
    (Sum.inl : MachineFieldTemplate.Label (tokens C).length → Label C)
    (some (.inr false)) (program C) (fun _ => rfl) (tapes word [])
    (by simp [tapes]) initialState
  have copy' : StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) word)
      (some ⟨some (.inr false), initialState, tapes word (copies C word).reverse⟩)
      (3 * (C * word.length) + 3 * C + 1) := by
    rw [initList_eq]
    simpa only [FinTM2.step, FinTM2.Cfg, machine, MachineFieldTemplate.reset, initialState,
      show (tapes word []) 0 = word from rfl,
      templateOutput, copiedLength, tokens_length, copied_tapes] using! copy
  have drain := MachineDrain.drainInTime (0 : Tape) (.inr false : Label C)
    (some (.inr true)) (program C) rfl (tapes word (copies C word).reverse) ((), ()) none
  have drain' : StateTransition.EvalsToInTime (machine C).step
      ⟨some (.inr false), initialState, tapes word (copies C word).reverse⟩
      (some ⟨some (.inr true), initialState, tapes [] (copies C word).reverse⟩)
      (word.length + 1) := by
    simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState,
      show (tapes word (copies C word).reverse) 0 = word from rfl,
      drained_tapes] using! drain
  have reverse := MachineTransfer.transferAtInTime (2 : Tape) 0 (by decide)
    id false (.inr true : Label C) none (program C) rfl
    (tapes [] (copies C word).reverse) ((), ()) none
  have reverse' : StateTransition.EvalsToInTime (machine C).step
      ⟨some (.inr true), initialState, tapes [] (copies C word).reverse⟩
      (some (haltList (machine C) (copies C word))) (C * word.length + 1) := by
    rw [haltList_eq]
    simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState,
      show (tapes [] (copies C word).reverse) 2 = (copies C word).reverse from rfl,
      show (tapes [] (copies C word).reverse) 0 = [] from rfl, List.reverse_reverse,
      List.map_id, List.append_nil, List.length_reverse, copies_length,
      transferred_tapes] using! reverse
  have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copy' drain'
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first reverse'
  exact {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by
      have h := whole.steps_le_m
      nlinarith }

/-- Its linear polynomial is measured in the actual input bit length. -/
noncomputable def computableInPolyTime (C : Nat) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id (copies C) where
  tm := machine C
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C (4 * C + 1) * Polynomial.X + Polynomial.C (3 * C + 3)
  outputsFun word := by
    change TM2OutputsInTime (machine C) (word.map id) (some ((copies C word).map id)) _
    have input_eq : @List.map ((machine C).Γ (machine C).k₀)
        ((machine C).Γ (machine C).k₀) id word = word := List.map_id word
    have output_eq : @List.map ((machine C).Γ (machine C).k₁)
        ((machine C).Γ (machine C).k₁) id (copies C word) = copies C word :=
      List.map_id (copies C word)
    simpa only [input_eq, output_eq, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Nat.add_assoc] using outputInTime C word

theorem computation_finiteAlphabet (C : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime C).tm := by
  intro k
  change Finite Bool
  infer_instance

end UniqueGamesTheorem.Explicit.MachineFixedCopies

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionRows

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction

def identityTable (q : Nat) : PermutationTable q where
  images := Vector.ofFn id
  inverseImages := Vector.ofFn id
  leftInverse _ := by simp
  rightInverse _ := by simp

def inverseTable {q : Nat} (p : PermutationTable q) : PermutationTable q where
  images := p.inverseImages
  inverseImages := p.images
  leftInverse := p.rightInverse
  rightInverse := p.leftInverse

/-- The saved fields are ordered `u,p,q,r,v`. All four edges are oriented
left-to-right; hence the last permutation is inverted. -/
def rows {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List (Constraint n q) :=
  [⟨vertices 0, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 3, identityTable q⟩,
   ⟨vertices 4, vertices 3, inverseTable p⟩]

@[simp] theorem rows_length {n q : Nat}
    (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    (rows vertices p).length = 4 := rfl

/-- The program copies saved endpoint words and emits complete forward tables. -/
def tokens (identity inverse : List Bool) : List (MachineFieldTemplate.Token 5) :=
  [.copy 0, .copy 1, .literal identity,
   .copy 2, .copy 1, .literal identity,
   .copy 2, .copy 3, .literal identity,
   .copy 4, .copy 3, .literal inverse]

@[simp] theorem tokens_length (identity inverse : List Bool) :
    (tokens identity inverse).length = 12 := rfl

def fields {n : Nat} (vertices : Fin 5 → Fin n) (j : Fin 5) : List Bool :=
  encodeWord (vertices j).val

def rowBits {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List Bool := encodeWords ((rows vertices p).flatMap constraintWords)

theorem templateOutput_rows {n q : Nat}
    (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    MachineFieldTemplate.templateOutput
        (tokens (encodeWords (tableWords (identityTable q)))
          (encodeWords (tableWords (inverseTable p)))) (fields vertices) =
      rowBits vertices p := by
  simp [MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput,
    tokens, fields, rowBits, rows, constraintWords, encodeWords]

/-- A finite stack layout: five preserved fields, scratch, and reversed output. -/
def field (j : Fin 5) : Fin 7 := ⟨j.val, by omega⟩

def scratch : Fin 7 := 5
def output : Fin 7 := 6

theorem field_ne_scratch (j : Fin 5) : field j ≠ scratch := by
  intro h
  have := congrArg Fin.val h
  simp [field, scratch] at this
  omega

theorem field_ne_output (j : Fin 5) : field j ≠ output := by
  intro h
  have := congrArg Fin.val h
  simp [field, output] at this
  omega

theorem scratch_ne_output : scratch ≠ output := by decide

def machine (identity inverse : List Bool) : FinTM2 where
  K := Fin 7
  k₀ := field 0
  k₁ := output
  Γ _ := Bool
  Λ := MachineFieldTemplate.Label (tokens identity inverse).length
  main := MachineFieldTemplate.startAt (tokens identity inverse).length 0
  σ := MachineFieldTemplate.State Unit
  initialState := (((), ()), none)
  m := MachineFieldTemplate.program (tokens identity inverse) field scratch output none

theorem machine_finiteAlphabet (identity inverse : List Bool) :
    ∀ k, Finite ((machine identity inverse).Γ k) := by
  intro k
  change Finite Bool
  infer_instance

/-- Exact physical row execution, preserving the five saved fields and restoring
scratch. This is a phase theorem; it does not assume its own execution. -/
def phaseInTime (identity inverse : List Bool) (base : Fin 7 → List Bool)
    (emptyScratch : base scratch = []) (state : MachineFieldTemplate.State Unit) :
    StateTransition.EvalsToInTime (machine identity inverse).step
      ⟨some (MachineFieldTemplate.startAt (tokens identity inverse).length 0), state, base⟩
      (some ⟨none, MachineFieldTemplate.reset state,
        MachineFieldTemplate.outputTapes base output
          (MachineFieldTemplate.templateOutput (tokens identity inverse)
            (fun j => base (field j)))⟩)
      (3 * MachineFieldTemplate.copiedLength (tokens identity inverse)
        (fun j => base (field j)) + 37) := by
  exact MachineFieldTemplate.phaseInTime (tokens identity inverse) field scratch output
    field_ne_scratch field_ne_output scratch_ne_output id none
    (MachineFieldTemplate.program (tokens identity inverse) field scratch output none)
    (fun _ => rfl) base emptyScratch state

theorem phase_budget (identity inverse : List Bool) (base : Fin 7 → List Bool) :
    3 * MachineFieldTemplate.copiedLength (tokens identity inverse)
        (fun j => base (field j)) + 37 =
      3 * ((base (field 0)).length + 2 * (base (field 1)).length +
        2 * (base (field 2)).length + 2 * (base (field 3)).length +
        (base (field 4)).length) + 37 := by
  simp [MachineFieldTemplate.copiedLength, tokens]
  omega

/-- The semantic subdivision numbering: originals and middle vertices on the
left, then two private right vertices for each occurrence. -/
def subdivisionVertexWords (n Q u v e : Nat) : Fin 5 → Nat
  | 0 => u
  | 1 => n + Q + 2 * e
  | 2 => n + e
  | 3 => n + Q + 2 * e + 1
  | 4 => v

theorem subdivisionVertexWords_bounded {n Q u v e : Nat}
    (hu : u < n) (hv : v < n) (he : e < Q) (j : Fin 5) :
    subdivisionVertexWords n Q u v e j < n + 3 * Q := by
  fin_cases j <;> simp [subdivisionVertexWords] <;> omega

end UniqueGamesTheorem.Explicit.MachineSubdivisionRows

end OAI
