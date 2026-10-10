import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineTransducer
import OAI.Computability.DirectedFeedback.Encoding.FormulaEncoding

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionRows

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction

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

def rows {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List (Constraint n q) :=
  [⟨vertices 0, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 3, identityTable q⟩,
   ⟨vertices 4, vertices 3, inverseTable p⟩]

@[simp] theorem rows_length {n q : Nat}
    (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    (rows vertices p).length = 4 := rfl

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

end DFVSGames.Explicit.MachineSubdivisionRows


namespace DFVSGames.Reduction.Encoding

open Integration.BinaryLinear
open Foundations.Target

def sideEquiv (n : Nat) : Bool × Fin n ≃ Fin (2*n) :=
  (finTwoEquiv.symm.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv

@[simp] theorem sideEquiv_false_val {n : Nat} (i : Fin n) : (sideEquiv n (false, i)).val = i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv]

@[simp] theorem sideEquiv_true_val {n : Nat} (i : Fin n) : (sideEquiv n (true, i)).val = n + i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv, Nat.add_comm]

def alphabetEquiv (s : Nat) : Integration.BinaryLinear.Vector s ≃ Fin (2^s) :=
  (coordinatesEquiv s).symm.trans
    { toFun := BitVec.toFin
      invFun := BitVec.ofFin
      left_inv := BitVec.ofFin_toFin
      right_inv := BitVec.toFin_ofFin }

@[simp] theorem alphabetEquiv_symm_apply_apply (s : Nat)
    (c : Integration.BinaryLinear.Vector s) :
    (alphabetEquiv s).symm (alphabetEquiv s c) = c :=
  (alphabetEquiv s).symm_apply_apply c

@[simp] theorem alphabetEquiv_apply_symm_apply (s : Nat) (c : Fin (2^s)) :
    alphabetEquiv s ((alphabetEquiv s).symm c) = c :=
  (alphabetEquiv s).apply_symm_apply c

def translate {s : Nat} (a b : Integration.BinaryLinear.Vector s)
    (c : Fin (2^s)) : Fin (2^s) :=
  alphabetEquiv s ((alphabetEquiv s).symm c + a + b)

theorem translate_involutive {s : Nat} (a b : Integration.BinaryLinear.Vector s) :
    Function.Involutive (translate a b) := by
  intro c
  simp only [translate, alphabetEquiv_symm_apply_apply]
  have h : (alphabetEquiv s).symm c + a + b + a + b = (alphabetEquiv s).symm c := by
    ext i
    simp only [Pi.add_apply]
    rw [show (alphabetEquiv s).symm c i + a i + b i + a i + b i =
      (alphabetEquiv s).symm c i + (a i + a i) + (b i + b i) by abel]
    simp [CharTwo.add_self_eq_zero]
  rw [h, alphabetEquiv_apply_symm_apply]

def translationTable {s : Nat} (a b : Integration.BinaryLinear.Vector s) :
    PermutationTable (2^s) where
  images := _root_.Vector.ofFn (translate a b)
  inverseImages := _root_.Vector.ofFn (translate a b)
  leftInverse c := by simpa using translate_involutive a b c
  rightInverse c := by simpa using translate_involutive a b c

@[simp] theorem translationTable_images {s : Nat}
    (a b c : Integration.BinaryLinear.Vector s) :
    (translationTable a b).images[alphabetEquiv s c] = alphabetEquiv s (c + a + b) := by
  simp [translationTable, translate]

@[simp] theorem translationTable_inverseImages {s : Nat}
    (a b c : Integration.BinaryLinear.Vector s) :
    (translationTable a b).inverseImages[alphabetEquiv s c] =
      alphabetEquiv s (c + a + b) := by
  simp [translationTable, translate]

theorem translationTable_satisfied_iff {s : Nat}
    (a b cLeft cRight : Integration.BinaryLinear.Vector s) :
    (translationTable a b).images[alphabetEquiv s cLeft] = alphabetEquiv s cRight ↔
      cLeft + a + b = cRight := by
  rw [translationTable_images]
  exact (alphabetEquiv s).injective.eq_iff


variable {Q V : Type*} [DecidableEq V]

def imageVertices (queries : List Q) (body : Q → V) : List V :=
  (queries.map body).dedup

theorem mem_imageVertices {queries : List Q} {body : Q → V} {v : V} :
    v ∈ imageVertices queries body ↔ ∃ q ∈ queries, body q = v := by
  simp [imageVertices]

theorem imageVertices_nodup (queries : List Q) (body : Q → V) :
    (imageVertices queries body).Nodup := List.nodup_dedup _

theorem imageVertices_length_le (queries : List Q) (body : Q → V) :
    (imageVertices queries body).length ≤ queries.length := by
  simpa only [imageVertices, List.length_map] using
    (List.dedup_sublist (queries.map body)).length_le

abbrev ImageVertex (queries : List Q) (body : Q → V) :=
  {v : V // v ∈ imageVertices queries body}

def imageEquiv (queries : List Q) (body : Q → V) :
    ImageVertex queries body ≃ Fin (imageVertices queries body).length :=
  (List.Nodup.getEquiv _ (imageVertices_nodup queries body)).symm

def imageVertex (queries : List Q) (body : Q → V) (q : Q) (hq : q ∈ queries) :
    ImageVertex queries body := ⟨body q, mem_imageVertices.mpr ⟨q, hq, rfl⟩⟩

def imageIndex (queries : List Q) (body : Q → V) (q : Q) (hq : q ∈ queries) :
    Fin (imageVertices queries body).length := imageEquiv queries body (imageVertex queries body q hq)

theorem imageIndex_eq_iff (queries : List Q) (body : Q → V)
    (q r : Q) (hq : q ∈ queries) (hr : r ∈ queries) :
    imageIndex queries body q hq = imageIndex queries body r hr ↔ body q = body r := by
  simp only [imageIndex, (imageEquiv queries body).injective.eq_iff, Subtype.mk.injEq,
    imageVertex]

theorem imageVertices_range (queries : List Q) (body : Q → V)
    (full : ∀ q, q ∈ queries) (v : V) :
    v ∈ imageVertices queries body ↔ v ∈ Set.range body := by
  simp [mem_imageVertices, full, Set.mem_range]


end DFVSGames.Reduction.Encoding


namespace DFVSGames.Explicit.MachineSubdivisionDynamicRows

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionRows (identityTable inverseTable)

def rows {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List (Constraint n q) :=
  [⟨vertices 0, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 3, identityTable q⟩,
   ⟨vertices 4, vertices 3, p⟩]

def tokens (identity : List Bool) : List (MachineFieldTemplate.Token 6) :=
  [.copy 0, .copy 1, .literal identity,
   .copy 2, .copy 1, .literal identity,
   .copy 2, .copy 3, .literal identity,
   .copy 4, .copy 3, .copy 5]

@[simp] theorem tokens_length (identity : List Bool) :
    (tokens identity).length = 12 := rfl

def fields {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    Fin 6 → List Bool :=
  ![encodeWord (vertices 0).val, encodeWord (vertices 1).val,
    encodeWord (vertices 2).val, encodeWord (vertices 3).val,
    encodeWord (vertices 4).val, encodeWords (tableWords p)]

def rowBits {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List Bool := encodeWords ((rows vertices p).flatMap constraintWords)

theorem templateOutput_rows {n q : Nat} (vertices : Fin 5 → Fin n)
    (p : PermutationTable q) :
    MachineFieldTemplate.templateOutput
      (tokens (encodeWords (tableWords (identityTable q)))) (fields vertices p) =
      rowBits vertices p := by
  simp [MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput,
    tokens, fields, rowBits, rows, constraintWords, encodeWords]

def field (j : Fin 6) : Fin 8 := ⟨j.val, by omega⟩

def scratch : Fin 8 := 6
def output : Fin 8 := 7

theorem field_ne_scratch (j : Fin 6) : field j ≠ scratch := by
  intro h
  have := congrArg Fin.val h
  simp [field, scratch] at this
  omega

theorem field_ne_output (j : Fin 6) : field j ≠ output := by
  intro h
  have := congrArg Fin.val h
  simp [field, output] at this
  omega

theorem scratch_ne_output : scratch ≠ output := by decide

def machine (identity : List Bool) : FinTM2 where
  K := Fin 8
  k₀ := field 0
  k₁ := output
  Γ _ := Bool
  Λ := MachineFieldTemplate.Label (tokens identity).length
  main := MachineFieldTemplate.startAt (tokens identity).length 0
  σ := MachineFieldTemplate.State Unit
  initialState := (((), ()), none)
  m := MachineFieldTemplate.program (tokens identity) field scratch output none

theorem machine_finiteAlphabet (identity : List Bool) :
    ∀ k, Finite ((machine identity).Γ k) := by
  intro k
  change Finite Bool
  infer_instance

def phaseInTime (identity : List Bool) (base : Fin 8 → List Bool)
    (emptyScratch : base scratch = []) (state : MachineFieldTemplate.State Unit) :
    StateTransition.EvalsToInTime (machine identity).step
      ⟨some (MachineFieldTemplate.startAt (tokens identity).length 0), state, base⟩
      (some ⟨none, MachineFieldTemplate.reset state,
        MachineFieldTemplate.outputTapes base output
          (MachineFieldTemplate.templateOutput (tokens identity)
            (fun j => base (field j)))⟩)
      (3 * MachineFieldTemplate.copiedLength (tokens identity)
        (fun j => base (field j)) + 37) := by
  exact MachineFieldTemplate.phaseInTime (tokens identity) field scratch output
    field_ne_scratch field_ne_output scratch_ne_output id none
    (MachineFieldTemplate.program (tokens identity) field scratch output none)
    (fun _ => rfl) base emptyScratch state

theorem phase_budget (identity : List Bool) (base : Fin 8 → List Bool) :
    3 * MachineFieldTemplate.copiedLength (tokens identity)
        (fun j => base (field j)) + 37 =
      3 * ((base (field 0)).length + 2 * (base (field 1)).length +
        2 * (base (field 2)).length + 2 * (base (field 3)).length +
        (base (field 4)).length + (base (field 5)).length) + 37 := by
  simp [MachineFieldTemplate.copiedLength, tokens]
  omega

theorem translation_inverse {s : Nat}
    (a b : DFVSGames.Integration.BinaryLinear.Vector s) :
    inverseTable (Encoding.translationTable a b) = Encoding.translationTable a b := rfl

theorem translation_rows {n s : Nat} (vertices : Fin 5 → Fin n)
    (a b : DFVSGames.Integration.BinaryLinear.Vector s) :
    rows vertices (Encoding.translationTable a b) =
      MachineSubdivisionRows.rows vertices (Encoding.translationTable a b) := by
  simp only [rows, MachineSubdivisionRows.rows, translation_inverse]

end DFVSGames.Explicit.MachineSubdivisionDynamicRows


namespace DFVSGames.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def guard (counter : K) (bodyLabel exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek counter (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop counter (fun state _ => (state.1, none)) (.goto fun _ => bodyLabel))
      (.load (fun state => (state.1, none)) (.goto fun _ => exitLabel)))

def counterTapes (counter : K) (base : K → List Bool) (n : Nat)
    (suffix : List Bool) : K → List Bool :=
  Function.update base counter (encodeWord n ++ suffix)

@[simp] theorem counterTapes_counter (counter : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix counter = encodeWord n ++ suffix := by
  simp [counterTapes]

theorem counterTapes_other (counter other : K) (hne : other ≠ counter)
    (base : K → List Bool) (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix other = base other := by
  simp [counterTapes, hne]

omit [DecidableEq K] in
theorem guardPushBound (counter : K) (bodyLabel exitLabel : Λ) :
    Runtime.statementPushBound (guard (σ := σ) counter bodyLabel exitLabel) = 0 := by
  rfl

theorem stepAux_succ (counter : K) (bodyLabel exitLabel : Λ)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard counter bodyLabel exitLabel) (ambient, register)
      (counterTapes counter base (n + 1) suffix) =
      ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  simp [guard, TM2.stepAux, counterTapes, encodeWord, List.replicate_succ]

theorem stepAux_zero (counter : K) (bodyLabel exitLabel : Λ)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard counter bodyLabel exitLabel) (ambient, register)
      (counterTapes counter base 0 suffix) =
      ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  simp [guard, TM2.stepAux, counterTapes, encodeWord]

theorem guardStep_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some guardLabel, (ambient, register), counterTapes counter base (n + 1) suffix⟩ =
      some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  change some (TM2.stepAux (program guardLabel) (ambient, register)
    (counterTapes counter base (n + 1) suffix)) = _
  rw [atGuard, stepAux_succ]

theorem guardStep_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩ =
      some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  change some (TM2.stepAux (program guardLabel) (ambient, register)
    (counterTapes counter base 0 suffix)) = _
  rw [atGuard, stepAux_zero]

theorem guardTrace_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some guardLabel, (ambient, register),
        counterTapes counter base (n + 1) suffix⟩) =
      some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    guardStep_succ counter guardLabel bodyLabel exitLabel program atGuard
      base n suffix ambient register

theorem guardTrace_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩) =
      some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    guardStep_zero counter guardLabel bodyLabel exitLabel program atGuard
      base suffix ambient register

def guardInTime_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, register), counterTapes counter base (n + 1) suffix⟩
      (some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    exact guardTrace_succ counter guardLabel bodyLabel exitLabel program atGuard
      base n suffix ambient register
  steps_le_m := Nat.le_refl _

def guardInTime_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩
      (some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    exact guardTrace_zero counter guardLabel bodyLabel exitLabel program atGuard
      base suffix ambient register
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineUnaryCounter


namespace DFVSGames.Explicit.MachineSubdivisionProgram

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open DFVSGames.Reduction

inductive Tape
  | input | vertices | alphabetHeader | occurrences | remaining
  | newVertices | newEdges | u | v | middle | first | last
  | permutation | permutationReverse | affineScratch | copyScratch
  | accumulator | output
  deriving DecidableEq

instance : Fintype Tape := derive_fintype% _

abbrev State := MachineFieldTemplate.State Unit

def initialState : State := (((), ()), none)

def headerField : Fin 3 → Tape
  | 0 => .vertices
  | 1 => .alphabetHeader
  | 2 => .occurrences

def rowField : Fin 6 → Tape
  | 0 => .u
  | 1 => .first
  | 2 => .middle
  | 3 => .last
  | 4 => .v
  | 5 => .permutation

def rowTokens (q : Nat) := MachineSubdivisionDynamicRows.tokens
  (encodeWords (tableWords (MachineSubdivisionRows.identityTable q)))

def headerTokens (q : Nat) : List (MachineFieldTemplate.Token 2) :=
  [.copy 0, .literal (encodeWord q), .copy 1]

def newHeaderField : Fin 2 → Tape
  | 0 => .newVertices
  | 1 => .newEdges

structure InitOp where
  source : Tape
  destination : Tape
  coefficient : Nat
  seed : Option Nat

def initOp : Fin 9 → InitOp
  | 0 => ⟨.vertices, .newVertices, 1, some 0⟩
  | 1 => ⟨.occurrences, .newVertices, 3, none⟩
  | 2 => ⟨.occurrences, .newEdges, 4, some 0⟩
  | 3 => ⟨.vertices, .middle, 1, some 0⟩
  | 4 => ⟨.vertices, .first, 1, some 0⟩
  | 5 => ⟨.occurrences, .first, 1, none⟩
  | 6 => ⟨.vertices, .last, 1, some 1⟩
  | 7 => ⟨.occurrences, .last, 1, none⟩
  | 8 => ⟨.occurrences, .remaining, 1, some 0⟩

def clearKeys : List Tape :=
  [.input, .vertices, .alphabetHeader, .occurrences, .remaining,
   .newVertices, .newEdges, .u, .v, .middle, .first, .last,
   .permutation, .permutationReverse, .affineScratch, .copyScratch]

inductive Label (q : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | initialize (i : Fin 9) (phase : Fin 3)
  | emitHeader (label : MachineFieldTemplate.Label (headerTokens q).length)
  | guard
  | startU | readU | startV | readV
  | readTable (completed : Fin (q + 1))
  | reverseTable
  | emitRows (label : MachineFieldTemplate.Label (rowTokens q).length)
  | drainU | drainV | drainPermutation
  | increment
  | finishStart
  | finish (label : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

def headerNext {q : Nat} (i : Fin 3) : Label q :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .initialize 0 0

def initNext {q : Nat} (i : Fin 9) : Label q :=
  if h : i.val + 1 < 9 then .initialize ⟨i.val + 1, h⟩ 0
  else .emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)

def rowEntry (q : Nat) : Label q :=
  .emitRows (MachineFieldTemplate.startAt (rowTokens q).length 0)

def program (q : Nat) : Label q → TM2.Stmt (fun _ : Tape => Bool) (Label q) State
  | .headerStart i => SourceMachine.fieldStart (headerField i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .input (headerField i)
      (.headerRead i) (some (headerNext i))
  | .initialize i 0 =>
      match (initOp i).seed with
      | some offset => MachineUnaryAffineAt.seed (initOp i).destination offset (.initialize i 1)
      | none => .goto (fun _ => .initialize i 1)
  | .initialize i 1 => MachineUnaryAffineAt.scan (initOp i).source .affineScratch
      (initOp i).destination (initOp i).coefficient (.initialize i 1) (.initialize i 2)
  | .initialize i 2 => MachineTransfer.loopAt .affineScratch (initOp i).source
      id false (.initialize i 2) (some (initNext i))
  | .emitHeader label => MachineFieldTemplate.instruction (headerTokens q)
      newHeaderField .copyScratch .accumulator Label.emitHeader (some .guard) label
  | .guard => MachineUnaryCounter.guard .remaining .startU .finishStart
  | .startU => SourceMachine.fieldStart .u .readU
  | .readU => SourceMachine.fieldLoop .input .u .readU (some .startV)
  | .startV => SourceMachine.fieldStart .v .readV
  | .readV => SourceMachine.fieldLoop .input .v .readV (some (.readTable 0))
  | .readTable completed =>
      if h : completed.val < q then
        .pop .input (fun state head => (state.1, head))
          (.push .permutationReverse (fun state => state.2.getD false)
            (.branch (fun state => state.2.getD false)
              (.goto fun _ => .readTable completed)
              (.load (fun state => (state.1, none))
                (.goto fun _ => .readTable ⟨completed.val + 1, by omega⟩))))
      else .load (fun state => (state.1, none)) (.goto fun _ => .reverseTable)
  | .reverseTable => MachineTransfer.loopAt .permutationReverse .permutation
      id false .reverseTable (some (rowEntry q))
  | .emitRows label => MachineFieldTemplate.instruction (rowTokens q)
      rowField .copyScratch .accumulator Label.emitRows (some .drainU) label
  | .drainU => MachineDrain.drain .u .drainU (some .drainV)
  | .drainV => MachineDrain.drain .v .drainV (some .drainPermutation)
  | .drainPermutation => MachineDrain.drain .permutation .drainPermutation (some .increment)
  | .increment => .push .middle (fun _ => true)
      (.push .first (fun _ => true) (.push .first (fun _ => true)
        (.push .last (fun _ => true) (.push .last (fun _ => true)
          (.load (fun _ => initialState) (.goto fun _ => .guard))))))
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      ((), ()) Label.finish none label

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label q
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program q

theorem machine_finiteAlphabet (q : Nat) :
    ∀ k, Finite ((machine q).Γ k) := by
  intro k
  change Finite Bool
  infer_instance

theorem rowField_injective : Function.Injective rowField := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [rowField]

theorem clearKeys_covers (k : Tape) :
    k ∈ clearKeys ∨ k = .accumulator ∨ k = .output := by
  cases k <;> simp [clearKeys]

theorem accumulator_not_mem_clearKeys : Tape.accumulator ∉ clearKeys := by decide
theorem output_not_mem_clearKeys : Tape.output ∉ clearKeys := by decide

end DFVSGames.Explicit.MachineSubdivisionProgram


namespace DFVSGames.Explicit.MachineSubdivisionHeaders

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineSubdivisionProgram

def inputTapes (bits : List Bool) : Tape → List Bool :=
  fun k => if k = .input then bits else []

def afterVertices (n : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n else []

def afterAlphabet (n q : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n
    else if k = .alphabetHeader then encodeWord q else []

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun k => if k = .input then body else if k = .vertices then encodeWord n
    else if k = .alphabetHeader then encodeWord q
    else if k = .occurrences then encodeWord Q else []

theorem initList_eq (q : Nat) (bits : List Bool) :
    initList (machine q) bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1

theorem first_result (n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .vertices
      (inputTapes (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes (encodeWord n ++ rest) .vertices) =
      afterVertices n rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices]

theorem second_result (n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .alphabetHeader
      (afterVertices n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices n (encodeWord q ++ rest) .alphabetHeader) =
      afterAlphabet n q rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet]

theorem third_result (n q Q : Nat) (body : List Bool) :
    SourceMachine.fieldTapes Tape.input .occurrences
      (afterAlphabet n q (encodeWord Q ++ body)) body
      (encodeWord Q ++ afterAlphabet n q (encodeWord Q ++ body) .occurrences) =
      resultTapes n q Q body := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterAlphabet, resultTapes]

def headersInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (encodeWords [n, q, Q] ++ body))
      (some ⟨some (.initialize 0 0), initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6) := by
  have first := SourceMachine.fieldInTime Tape.input .vertices (by decide)
    (.headerStart 0 : Label q) (.headerRead 0) (some (.headerStart 1))
    (program q) rfl rfl
    (inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))) n
    (encodeWord q ++ (encodeWord Q ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime Tape.input .alphabetHeader (by decide)
    (.headerStart 1 : Label q) (.headerRead 1) (some (.headerStart 2))
    (program q) rfl rfl (afterVertices n (encodeWord q ++ (encodeWord Q ++ body))) q
    (encodeWord Q ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime Tape.input .occurrences (by decide)
    (.headerStart 2 : Label q) (.headerRead 2) (some (.initialize 0 0))
    (program q) rfl rfl (afterAlphabet n q (encodeWord Q ++ body)) Q body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  change StateTransition.EvalsToInTime (TM2.step (program q))
    ⟨some (.headerStart 0), initialState, inputTapes (encodeWords [n, q, Q] ++ body)⟩
    (some ⟨some (.initialize 0 0), initialState, resultTapes n q Q body⟩)
    (n + q + Q + 6)
  simpa only [encodeWords, List.nil_append, List.append_assoc]
    using ({
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        omega } : StateTransition.EvalsToInTime (TM2.step (program q))
        ⟨some (.headerStart 0), initialState,
          inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))⟩
        (some ⟨some (.initialize 0 0), initialState, resultTapes n q Q body⟩)
        (n + q + Q + 6))

theorem headers_budget (q n Q : Nat) (body : List Bool) :
    n + q + Q + 6 ≤ (encodeWords [n, q, Q] ++ body).length + 3 := by
  simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  omega

end DFVSGames.Explicit.MachineSubdivisionHeaders

end OAI
