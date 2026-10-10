import Mathlib
import OAI.Computability.MaxCut.Encoding.FormulaEncoding
import OAI.Computability.MaxCut.Machines.MachineFieldTemplate

namespace OAI

namespace MaxCutGames.Explicit.MachineSubdivisionRows

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction

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

end MaxCutGames.Explicit.MachineSubdivisionRows

end OAI
