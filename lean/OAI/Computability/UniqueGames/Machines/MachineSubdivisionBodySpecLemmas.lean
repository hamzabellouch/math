import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.DeriveFintype
import OAI.Computability.UniqueGames.Games.SubdivisionEncoding
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.Machines.MachineSubdivisionBody
import OAI.Computability.UniqueGames.Machines.MachineSubdivisionDynamicRowsLemmas
import OAI.Computability.UniqueGames.Machines.MachineUnaryAffineAt
import OAI.Computability.UniqueGames.PCP.SourceLoopInitLemmas
import OAI.Computability.UniqueGames.PCP.SourceMachine
import OAI.Computability.UniqueGames.Reduction.MachineFieldTemplate

namespace OAI

noncomputable section

/-! Exact tape framing, row serialization, and a uniform polynomial bound for
the already constructed whole subdivision-body execution. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionBodySpec

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram MachineSubdivisionBody

def resultTapes {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .u | .v | .permutation | .permutationReverse => []
  | .middle => true :: base .middle
  | .first => true :: true :: base .first
  | .last => true :: true :: base .last
  | .accumulator => (rowPayload base u v table suffix).reverse ++ base .accumulator
  | k => base k

/-- Every tape at the body boundary, including all preserved headers and counters. -/
theorem bodyResult_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix = resultTapes base u v table suffix := by
  cases ready
  funext k
  cases k <;> simp [bodyResult, incrementTapes, afterDrainTable, afterDrainV,
    afterDrainU, afterRows, MachineFieldTemplate.outputTapes, afterTable,
    MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes, resultTapes]

theorem result_input {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .input = suffix := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem result_locals {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .u = [] ∧
    bodyResult base u v table suffix .v = [] ∧
    bodyResult base u v table suffix .permutation = [] ∧
    bodyResult base u v table suffix .permutationReverse = [] ∧
    bodyResult base u v table suffix .copyScratch = [] := by
  rw [bodyResult_eq base u v table suffix ready]
  simp [resultTapes, ready.scratchEmpty]

theorem result_accumulator {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .accumulator =
      (rowPayload base u v table suffix).reverse ++ base .accumulator := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem encodeWord_succ (n : Nat) : encodeWord (n + 1) = true :: encodeWord n := by
  simp [encodeWord, List.replicate_succ]

theorem result_indices {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyResult base u v table suffix .middle = encodeWord (n + (e + 1)) ∧
    bodyResult base u v table suffix .first = encodeWord (n + Q + 2 * (e + 1)) ∧
    bodyResult base u v table suffix .last = encodeWord (n + Q + 2 * (e + 1) + 1) := by
  rw [bodyResult_eq base u v table suffix ready]
  have hm : n + (e + 1) = (n + e) + 1 := by omega
  have hf : n + Q + 2 * (e + 1) = (n + Q + 2 * e) + 1 + 1 := by omega
  simp [resultTapes, middle, first, last, hm, hf, encodeWord_succ]

/-- Four whole rows, with the final table already in left-to-right orientation. -/
def rowBits {q : Nat} (u middle first last v : Nat) (table : Target.PermutationTable q) :
    List Bool :=
  encodeWords
    ([u, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, last] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [v, last] ++ tableWords table)

theorem rowPayload_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (middle first last : Nat)
    (hm : base .middle = encodeWord middle) (hf : base .first = encodeWord first)
    (hl : base .last = encodeWord last) :
    rowPayload base u v table suffix = rowBits u middle first last v table := by
  simp [rowPayload, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput, rowField,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, hm, hf, hl,
    rowBits, tableBits, encodeWords, List.append_assoc]

/-- The natural-word description is literally the established finite-target
constraint codec, rather than an alternative encoding. -/
theorem rowBits_eq_dynamic {N q : Nat} (vertices : Fin 5 → Fin N)
    (table : Target.PermutationTable q) :
    rowBits (vertices 0).val (vertices 2).val (vertices 1).val (vertices 3).val
      (vertices 4).val table = MachineSubdivisionDynamicRows.rowBits vertices table := by
  simp [rowBits, MachineSubdivisionDynamicRows.rowBits, MachineSubdivisionDynamicRows.rows,
    constraintWords, List.append_assoc]

/-- One conservative bound uniform over all occurrences in this output.
Only the fixed alphabet and the runtime header sizes appear in the polynomial. -/
theorem bodyBudget_le {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (hu : u < n) (hv : v < n) (he : e ≤ Q)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyBudget base u v table suffix ≤ 100 * (n + 3 * Q + q * (q + 1) + 1) := by
  have ht : (tableBits table).length ≤ q * (q + 1) :=
    GameEncodingSize.tableBits_length_le table
  simp [bodyBudget, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.copiedLength, rowField,
    afterDrainV, afterDrainU, afterRows, MachineFieldTemplate.outputTapes,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, middle, first, last] at *
  omega

end UniqueGamesTheorem.Explicit.MachineSubdivisionBodySpec

/-! Concrete frames and literal row words for the subdivision occurrence loop. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionLoopFrame

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

def bodyBits {n q : Nat} (edges : List (Constraint n q)) : List Bool :=
  encodeWords (edges.flatMap constraintWords)

@[simp] theorem bodyBits_nil {n q : Nat} : bodyBits ([] : List (Constraint n q)) = [] := rfl

theorem bodyBits_cons {n q : Nat} (edge : Constraint n q) (edges : List (Constraint n q)) :
    bodyBits (edge :: edges) =
      encodeWord edge.source.val ++ encodeWord edge.target.val ++
        MachineSubdivisionBody.tableBits edge.permutation ++ bodyBits edges := by
  simp [bodyBits, constraintWords, encodeWords, MachineSubdivisionBody.tableBits,
    List.append_assoc]

def identityBits (q : Nat) : List Bool :=
  encodeWords (tableWords (MachineSubdivisionRows.identityTable q))

def rowBits {n q : Nat} (Q e : Nat) (edge : Constraint n q) : List Bool :=
  encodeWords [edge.source.val, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e + 1] ++ identityBits q ++
  encodeWords [edge.target.val, n + Q + 2 * e + 1] ++
    MachineSubdivisionBody.tableBits edge.permutation

def outputRows {n q : Nat} (Q : Nat) : Nat → List (Constraint n q) → List Bool
  | _, [] => []
  | e, edge :: edges => rowBits Q e edge ++ outputRows Q (e + 1) edges

def frame {n q : Nat} (Q e : Nat) (edges : List (Constraint n q))
    (emitted : List Bool) : Tape → List Bool :=
  fun tape => match tape with
  | .input => bodyBits edges
  | .remaining => encodeWord edges.length
  | .middle => encodeWord (n + e)
  | .first => encodeWord (n + Q + 2 * e)
  | .last => encodeWord (n + Q + 2 * e + 1)
  | .accumulator => emitted.reverse
  | _ => MachineSubdivisionInit.resultTapes n q Q [] tape

def afterGuard {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) : Tape → List Bool :=
  Function.update (frame Q e (edge :: edges) emitted) .remaining (encodeWord edges.length)

theorem frame_prepared {n q : Nat} (edges : List (Constraint n q)) :
    frame edges.length 0 edges (MachineSubdivisionEmission.headerBits n q edges.length) =
      MachineSubdivisionEmission.resultTapes n q edges.length (bodyBits edges) := by
  funext tape
  cases tape <;> simp [frame, MachineSubdivisionEmission.resultTapes,
    MachineSubdivisionInit.resultTapes]

theorem guard_cons {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    (machine q).step ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩ =
      some ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩ := by
  have before : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e (edge :: edges) emitted) (edges.length + 1) [] =
      frame Q e (edge :: edges) emitted := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil]
    change Function.update (frame Q e (edge :: edges) emitted) Tape.remaining
      ((frame Q e (edge :: edges) emitted) .remaining) = _
    exact Function.update_eq_self _ _
  have after : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e (edge :: edges) emitted) edges.length [] =
      afterGuard Q e edge edges emitted := by
    simp [MachineUnaryCounter.counterTapes, afterGuard]
  have run := MachineUnaryCounter.guardStep_succ Tape.remaining
    (.guard : Label q) .startU .finishStart (program q) rfl
    (frame Q e (edge :: edges) emitted) edges.length [] ((), ()) none
  rw [before, after] at run
  simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState] using! run

theorem guard_nil (n q Q e : Nat) (emitted : List Bool) :
    (machine q).step
      ⟨some .guard, initialState, frame Q e ([] : List (Constraint n q)) emitted⟩ =
      some ⟨some .finishStart, initialState, frame Q e ([] : List (Constraint n q)) emitted⟩ := by
  have framed : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e ([] : List (Constraint n q)) emitted) 0 [] =
      frame Q e ([] : List (Constraint n q)) emitted := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil]
    change Function.update (frame Q e ([] : List (Constraint n q)) emitted) Tape.remaining
      ((frame Q e ([] : List (Constraint n q)) emitted) .remaining) = _
    exact Function.update_eq_self _ _
  have run := MachineUnaryCounter.guardStep_zero Tape.remaining
    (.guard : Label q) .startU .finishStart (program q) rfl
    (frame Q e ([] : List (Constraint n q)) emitted) [] ((), ()) none
  rw [framed] at run
  simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState] using! run

theorem ready {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.Ready (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) := by
  constructor
  · simpa only [afterGuard, Function.update_of_ne (by decide : Tape.input ≠ .remaining),
      frame] using bodyBits_cons edge edges
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]

end UniqueGamesTheorem.Explicit.MachineSubdivisionLoopFrame

/-! The actual streamed bytes coincide with the numbered semantic subdivision.
The controller copies the last table unchanged, so its input contract explicitly
requires involutive tables; binary translations satisfy this condition. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionCorrespondence

open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubdivisionLoopFrame

def Involutive {q : Nat} (H : Instance q) : Prop :=
  ∀ e : Fin H.constraints.length,
    MachineSubdivisionRows.inverseTable H.constraints[e].permutation = H.constraints[e].permutation

theorem inverseTable_eq {q : Nat} (p : PermutationTable q)
    (same : p.inverseImages = p.images) : MachineSubdivisionRows.inverseTable p = p := by
  cases p with
  | mk images inverseImages left right =>
    dsimp at same
    cases same
    rfl

theorem translations_involutive {q s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s) (H : Instance q)
    (translations : Integration.TranslationTarget.IsTranslationInstance coordinates H) :
    Involutive H := by
  intro e
  apply inverseTable_eq
  apply Vector.ext
  intro i hi
  apply coordinates.injective
  obtain ⟨shift, law⟩ := translations H.constraints[e] (List.getElem_mem e.isLt)
  have h := law (H.constraints[e].permutation.inverseImages[(⟨i, hi⟩ : Fin q)])
  rw [H.constraints[e].permutation.rightInverse] at h
  have cancel : shift + shift = 0 := by
    ext j
    simp [CharTwo.add_self_eq_zero]
  have doubled := congrArg (fun x => x + shift) h
  have inverseLaw : coordinates (H.constraints[e].permutation.inverseImages[(⟨i, hi⟩ : Fin q)]) =
      coordinates ⟨i, hi⟩ + shift := by
    simpa only [add_assoc, cancel, add_zero] using doubled.symm
  exact inverseLaw.trans (law ⟨i, hi⟩).symm

theorem rowBits_eq_semantic {q : Nat} (H : Instance q) (e : Fin H.constraints.length)
    (involutive : Involutive H) :
    rowBits H.constraints.length e.val H.constraints[e] =
      MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
        H.constraints[e].permutation := by
  have words := MachineSubdivisionBodySpec.rowBits_eq_dynamic
    (SubdivisionTarget.vertexFields H e) H.constraints[e].permutation
  have vertices (j : Fin 5) := SubdivisionTarget.vertexFields_val H e j
  simp only [MachineSubdivisionRows.subdivisionVertexWords] at vertices
  have dynamic : MachineSubdivisionDynamicRows.rowBits
      (SubdivisionTarget.vertexFields H e) H.constraints[e].permutation =
      MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
        H.constraints[e].permutation := by
    simp only [MachineSubdivisionDynamicRows.rowBits, MachineSubdivisionRows.rowBits,
      MachineSubdivisionDynamicRows.rows, MachineSubdivisionRows.rows, involutive e]
  rw [← dynamic, ← words]
  simp only [vertices, MachineSubdivisionBodySpec.rowBits, rowBits, identityBits,
    MachineSubdivisionBody.tableBits, encodeWords_append, List.append_assoc]

theorem outputRows_eq_ofFn {n q : Nat} (Q e : Nat) (edges : List (Constraint n q)) :
    outputRows Q e edges =
      (List.ofFn (fun i : Fin edges.length => rowBits Q (e + i.val) edges[i])).flatten := by
  induction edges generalizing e with
  | nil => rfl
  | cons edge edges ih =>
    rw [outputRows, ih, List.ofFn_succ]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem outputRows_eq_semantic {q : Nat} (H : Instance q) (involutive : Involutive H) :
    outputRows H.constraints.length 0 H.constraints =
      (List.finRange H.constraints.length).flatMap (fun e =>
        MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
          H.constraints[e].permutation) := by
  rw [outputRows_eq_ofFn]
  simp only [Nat.zero_add, rowBits_eq_semantic H _ involutive, List.ofFn_eq_map,
    List.flatMap_def]

/-- Exact complete serialized output, including the changed headers and every
forward permutation-table entry, in occurrence order. -/
theorem output_eq_gameBits {q : Nat} (H : Instance q) (involutive : Involutive H) :
    MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
      outputRows H.constraints.length 0 H.constraints =
      gameBits (SubdivisionTarget.subdivide H) := by
  rw [SubdivisionEncoding.subdivide_gameBits, outputRows_eq_semantic H involutive]
  rfl

end UniqueGamesTheorem.Explicit.MachineSubdivisionCorrespondence

/-! Complete physical occurrence traversal of the subdivision program. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionLoop

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame

theorem rowPayload_eq {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.rowPayload (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) = rowBits Q e edge := by
  rw [MachineSubdivisionBodySpec.rowPayload_eq _ _ _ _ _ (ready Q e edge edges emitted)
    (n + e) (n + Q + 2 * e) (n + Q + 2 * e + 1) rfl rfl rfl]
  simp only [MachineSubdivisionBodySpec.rowBits, rowBits, identityBits,
    MachineSubdivisionBody.tableBits, encodeWords_append, List.append_assoc]

theorem bodyResult_eq_frame {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.bodyResult (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) =
      frame Q (e + 1) edges (emitted ++ rowBits Q e edge) := by
  have indices := MachineSubdivisionBodySpec.result_indices
    (afterGuard Q e edge edges emitted) edge.source.val edge.target.val edge.permutation
    (bodyBits edges) (ready Q e edge edges emitted) n Q e rfl rfl rfl
  funext tape
  cases tape with
  | middle => exact indices.1
  | first => exact indices.2.1
  | last => exact indices.2.2
  | input => exact MachineSubdivisionBodySpec.result_input _ _ _ _ _ (ready Q e edge edges emitted)
  | accumulator =>
    rw [MachineSubdivisionBodySpec.result_accumulator _ _ _ _ _ (ready Q e edge edges emitted),
      rowPayload_eq]
    simp [afterGuard, frame, List.reverse_append]
  | _ =>
    rw [MachineSubdivisionBodySpec.bodyResult_eq _ _ _ _ _ (ready Q e edge edges emitted)]
    simp [MachineSubdivisionBodySpec.resultTapes, afterGuard, frame,
      MachineSubdivisionInit.resultTapes]

def bodyBound (n q Q : Nat) : Nat := 100 * (n + 3 * Q + q * (q + 1) + 1)

def bodyInTime {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) (he : e ≤ Q) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩
      (some ⟨some .guard, initialState, frame Q (e + 1) edges (emitted ++ rowBits Q e edge)⟩)
      (bodyBound n q Q) := by
  have run := MachineSubdivisionBody.bodyInTime (afterGuard Q e edge edges emitted)
    edge.source.val edge.target.val edge.permutation (bodyBits edges) (ready Q e edge edges emitted)
  rw [bodyResult_eq_frame] at run
  have bound := MachineSubdivisionBodySpec.bodyBudget_le (afterGuard Q e edge edges emitted)
    edge.source.val edge.target.val edge.permutation (bodyBits edges) (ready Q e edge edges emitted)
    n Q e edge.source.isLt edge.target.isLt he rfl rfl rfl
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := run.steps_le_m.trans bound }

/-- Every list occurrence is read once, emits exactly its four rows, and advances
the three private numeric names. The loop includes its final zero-counter test. -/
def loopInTime {n q : Nat} (Q e : Nat) (edges : List (Constraint n q))
    (emitted : List Bool) (fit : e + edges.length ≤ Q) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .guard, initialState, frame Q e edges emitted⟩
      (some ⟨some .finishStart, initialState,
        frame Q (e + edges.length) ([] : List (Constraint n q))
          (emitted ++ outputRows Q e edges)⟩)
      (edges.length * (bodyBound n q Q + 1) + 1) := by
  induction edges generalizing e emitted with
  | nil =>
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := by simp }
    change (machine q).step ⟨some .guard, initialState, frame Q e [] emitted⟩ = _
    simpa only [List.length_nil, Nat.add_zero, outputRows, List.append_nil]
      using guard_nil n q Q e emitted
  | cons edge edges ih =>
    have he : e ≤ Q := by simp only [List.length_cons] at fit; omega
    have remainingFit : (e + 1) + edges.length ≤ Q := by
      simp only [List.length_cons] at fit
      omega
    have guard : StateTransition.EvalsToInTime (machine q).step
        ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩
        (some ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩) 1 := {
      steps := 1
      evals_in_steps := by
        change (machine q).step
          ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩ = _
        exact guard_cons Q e edge edges emitted
      steps_le_m := Nat.le_refl _ }
    have body := bodyInTime Q e edge edges emitted he
    have tail := ih (e + 1) (emitted ++ rowBits Q e edge) remainingFit
    have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first tail
    have index_eq : (e + 1) + edges.length = e + (edge :: edges).length := by simp; omega
    have words_eq : (emitted ++ rowBits Q e edge) ++ outputRows Q (e + 1) edges =
        emitted ++ outputRows Q e (edge :: edges) := by
      simp only [outputRows, List.append_assoc]
    rw [index_eq, words_eq] at whole
    exact {
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega }

end UniqueGamesTheorem.Explicit.MachineSubdivisionLoop

/-! The complete finite subdivision machine, including its polynomial runtime
in the actual serialized input length and exact full-table output. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionRuntime

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame
open MachineSubdivisionCorrespondence

def prefixPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.X * (Polynomial.C 100 *
    (Polynomial.C 4 * Polynomial.X + Polynomial.C (q * (q + 1)) + 1) + 1) +
    Polynomial.C 62 * Polynomial.X + Polynomial.C (q + 50)

def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineSubdivisionFinish.timePolynomial q (prefixPolynomial q)

theorem input_eq {q : Nat} (H : Instance q) :
    gameBits H = encodeWords [H.vertices, q, H.constraints.length] ++ bodyBits H.constraints := by
  simp only [gameBits, gameWords, bodyBits, encodeWords_append]

theorem input_size {q : Nat} (H : Instance q) :
    H.vertices ≤ (gameBits H).length ∧ H.constraints.length ≤ (gameBits H).length := by
  rw [input_eq]
  simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  omega

def finalTapes {q : Nat} (H : Instance q) : Tape → List Bool :=
  frame H.constraints.length H.constraints.length ([] : List (Constraint H.vertices q))
    (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
      outputRows H.constraints.length 0 H.constraints)

theorem final_outputEmpty {q : Nat} (H : Instance q) : finalTapes H .output = [] := rfl

theorem final_accumulator {q : Nat} (H : Instance q) (involutive : Involutive H) :
    finalTapes H .accumulator = (gameBits (SubdivisionTarget.subdivide H)).reverse := by
  change (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
    outputRows H.constraints.length 0 H.constraints).reverse = _
  rw [output_eq_gameBits H involutive]

/-- The prefix contains every actual header read, fresh-name initialization,
header emission, complete four-row body, and occurrence-counter test. -/
def prefixInTime {q : Nat} (H : Instance q) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (gameBits H))
      (some ⟨some .finishStart, initialState, finalTapes H⟩)
      ((prefixPolynomial q).eval (gameBits H).length) := by
  have initial := MachineSubdivisionEmission.prepareInTime q H.vertices H.constraints.length
    (bodyBits H.constraints)
  rw [← input_eq H, ← frame_prepared H.constraints] at initial
  have loop := MachineSubdivisionLoop.loopInTime H.constraints.length 0 H.constraints
    (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length) (by simp)
  simp only [Nat.zero_add] at loop
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initial loop
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := ?_ }
  have hn := (input_size H).1
  have hQ := (input_size H).2
  have bodyBound : MachineSubdivisionLoop.bodyBound H.vertices q H.constraints.length + 1 ≤
      100 * (4 * (gameBits H).length + q * (q + 1) + 1) + 1 := by
    unfold MachineSubdivisionLoop.bodyBound
    omega
  have loopBound := Nat.mul_le_mul hQ bodyBound
  have prepBound : H.vertices + q + H.constraints.length + 6 +
      9 * MachineSubdivisionInit.stageCost H.vertices H.constraints.length +
      (3 * (H.vertices + 7 * H.constraints.length + 2) + 10) ≤
      62 * (gameBits H).length + q + 49 := by
    unfold MachineSubdivisionInit.stageCost
    omega
  have bound := whole.steps_le_m
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  omega

/-- Literal initialization to literal clean halting configuration, with exact
semantic subdivision output. No execution or runtime premise is assumed. -/
def fullRunInTime {q : Nat} (H : Instance q) (involutive : Involutive H) :
    TM2OutputsInTime (machine q) (gameBits H)
      (some (gameBits (SubdivisionTarget.subdivide H)))
      ((timePolynomial q).eval (gameBits H).length) := by
  have run := MachineSubdivisionFinish.completePrefix q (gameBits H) (prefixPolynomial q)
    (finalTapes H) (prefixInTime H) (final_outputEmpty H)
  simpa only [final_accumulator H involutive, List.reverse_reverse, timePolynomial] using run

/-- The input subtype records the mathematical involution property, while the
same finite transition program is used for every instance of the fixed alphabet. -/
def computableInPolyTime (q : Nat) :
    TM2ComputableInPolyTime
      (fun H : {H : Instance q // Involutive H} => gameBits H.val)
      gameBits (fun H => SubdivisionTarget.subdivide H.val) where
  tm := machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q
  outputsFun H := by
    change TM2OutputsInTime (machine q) ((gameBits H.val).map id)
      (some ((gameBits (SubdivisionTarget.subdivide H.val)).map id))
      ((timePolynomial q).eval (gameBits H.val).length)
    erw [List.map_id, List.map_id]
    exact fullRunInTime H.val H.property

def familyComputableInPolyTime {α : Type} {q : Nat} (f : α → Instance q)
    (involutive : ∀ a, Involutive (f a)) :
    TM2ComputableInPolyTime (fun a => gameBits (f a)) gameBits
      (fun a => SubdivisionTarget.subdivide (f a)) where
  tm := machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q
  outputsFun a := by
    change TM2OutputsInTime (machine q) ((gameBits (f a)).map id)
      (some ((gameBits (SubdivisionTarget.subdivide (f a))).map id))
      ((timePolynomial q).eval (gameBits (f a)).length)
    erw [List.map_id, List.map_id]
    exact fullRunInTime (f a) (involutive a)

theorem workAlphabetFinite (q : Nat) (tape : (computableInPolyTime q).tm.K) :
    Finite ((computableInPolyTime q).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end UniqueGamesTheorem.Explicit.MachineSubdivisionRuntime

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionCompose

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubdivisionCorrespondence

variable {α : Type} {q : Nat} {encode : α → List Bool} {f : α → Instance q}

def certifiedOutput (involutive : ∀ a, Involutive (f a)) (a : α) :
    {H : Instance q // Involutive H} := ⟨f a, involutive a⟩

/-- Attach the already-proved property without executing anything or changing
the input or output codec. -/
def certify (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a)) :
    TM2ComputableInPolyTime encode (fun H : {H : Instance q // Involutive H} => gameBits H.val)
      (certifiedOutput involutive) where
  tm := upstream.tm
  inputAlphabet := upstream.inputAlphabet
  outputAlphabet := upstream.outputAlphabet
  time := upstream.time
  outputsFun := upstream.outputsFun

def computableInPolyTime (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a)) :
    TM2ComputableInPolyTime encode gameBits (fun a => SubdivisionTarget.subdivide (f a)) :=
  MachineSequential.composeBits (f := certifiedOutput involutive)
    (g := fun H : {H : Instance q // Involutive H} => SubdivisionTarget.subdivide H.val)
    (certify upstream involutive)
    (MachineSubdivisionRuntime.computableInPolyTime q)

theorem finiteAlphabet (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a))
    (finite : MachineFiniteAlphabet.FiniteAlphabet upstream.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime upstream involutive).tm := by
  exact MachineFiniteAlphabet.composeBits (certify upstream involutive)
    (MachineSubdivisionRuntime.computableInPolyTime q) finite
    (MachineSubdivisionRuntime.workAlphabetFinite q)

/-- Binary-translation producers discharge the only table-law condition. -/
def translationComputableInPolyTime {s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s)
    (upstream : TM2ComputableInPolyTime encode gameBits f)
    (translations : ∀ a, Integration.TranslationTarget.IsTranslationInstance coordinates (f a)) :
    TM2ComputableInPolyTime encode gameBits (fun a => SubdivisionTarget.subdivide (f a)) :=
  computableInPolyTime upstream (fun a => translations_involutive coordinates (f a) (translations a))

end UniqueGamesTheorem.Explicit.MachineSubdivisionCompose

/-! A real finite program for uniform whole-instance copying. It reads three
headers, physically multiplies the occurrence count by the fixed constant,
copies the header-free body the same fixed number of times, and clears all
working tapes. No input-dependent data are placed in finite control. -/

namespace UniqueGamesTheorem.Explicit.MachineUniformProgram

open Turing UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Hastad

inductive Tape
  | input | vertices | alphabet | occurrences | newOccurrences
  | affineScratch | copyScratch | accumulator | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .vertices, .alphabet, .occurrences,
  .newOccurrences, .affineScratch, .copyScratch, .accumulator, .output]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State := MachineFieldTemplate.State Unit

def initialState : State := (((), ()), none)

def headerField : Fin 3 → Tape
  | 0 => .vertices
  | 1 => .alphabet
  | 2 => .occurrences

def emitField : Fin 4 → Tape
  | 0 => .vertices
  | 1 => .alphabet
  | 2 => .newOccurrences
  | 3 => .input

def tokens (C : Nat) : List (MachineFieldTemplate.Token 4) :=
  [.copy 0, .copy 1, .copy 2] ++ List.replicate C (.copy 3)

def clearKeys : List Tape :=
  [.input, .vertices, .alphabet, .occurrences, .newOccurrences,
    .affineScratch, .copyScratch]

inductive Label (C : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | scale (phase : Fin 3)
  | emit (label : MachineFieldTemplate.Label (tokens C).length)
  | finishStart
  | finish (label : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

def headerNext {C : Nat} (i : Fin 3) : Label C :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .scale 0

def emitEntry (C : Nat) : Label C :=
  .emit (MachineFieldTemplate.startAt (tokens C).length 0)

def program (C : Nat) : Label C → TM2.Stmt (fun _ : Tape => Bool) (Label C) State
  | .headerStart i => SourceMachine.fieldStart (headerField i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .input (headerField i)
      (.headerRead i) (some (headerNext i))
  | .scale 0 => MachineUnaryAffineAt.seed .newOccurrences 0 (.scale 1)
  | .scale 1 => MachineUnaryAffineAt.scan .occurrences .affineScratch
      .newOccurrences C (.scale 1) (.scale 2)
  | .scale 2 => MachineTransfer.loopAt .affineScratch .occurrences id false
      (.scale 2) (some (emitEntry C))
  | .emit label => MachineFieldTemplate.instruction (tokens C) emitField
      .copyScratch .accumulator Label.emit (some .finishStart) label
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      ((), ()) Label.finish none label

def machine (C : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label C
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program C

theorem covers (k : Tape) (ha : k ≠ .accumulator) (ho : k ≠ .output) :
    k ∈ clearKeys := by
  cases k <;> simp_all [clearKeys]

theorem accumulator_not_mem_clearKeys : Tape.accumulator ∉ clearKeys := by decide
theorem output_not_mem_clearKeys : Tape.output ∉ clearKeys := by decide

end UniqueGamesTheorem.Explicit.MachineUniformProgram

/-! Exact execution of the three input-header reads of uniform copying. -/

namespace UniqueGamesTheorem.Explicit.MachineUniformHeaders

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineUniformProgram

def inputTapes (bits : List Bool) : Tape → List Bool :=
  fun k => if k = .input then bits else []

def afterVertices (n : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n else []

def afterAlphabet (n q : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n
    else if k = .alphabet then encodeWord q else []

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun k => if k = .input then body else if k = .vertices then encodeWord n
    else if k = .alphabet then encodeWord q
    else if k = .occurrences then encodeWord Q else []

theorem initList_eq (C : Nat) (bits : List Bool) :
    initList (machine C) bits =
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
    SourceMachine.fieldTapes Tape.input .alphabet
      (afterVertices n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices n (encodeWord q ++ rest) .alphabet) =
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

/-- The input headers are consumed literally; all unread constraint bits retain
their original order and no tape contains an implicit runtime number. -/
def headersInTime (C q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6) := by
  have first := SourceMachine.fieldInTime Tape.input .vertices (by decide)
    (.headerStart 0 : Label C) (.headerRead 0) (some (.headerStart 1))
    (program C) rfl rfl
    (inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))) n
    (encodeWord q ++ (encodeWord Q ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime Tape.input .alphabet (by decide)
    (.headerStart 1 : Label C) (.headerRead 1) (some (.headerStart 2))
    (program C) rfl rfl (afterVertices n (encodeWord q ++ (encodeWord Q ++ body))) q
    (encodeWord Q ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime Tape.input .occurrences (by decide)
    (.headerStart 2 : Label C) (.headerRead 2) (some (.scale 0))
    (program C) rfl rfl (afterAlphabet n q (encodeWord Q ++ body)) Q body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  simpa only [encodeWords, List.nil_append, List.append_assoc, machine, FinTM2.step,
    FinTM2.Cfg, initialState]
    using! ({
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        omega } : StateTransition.EvalsToInTime (TM2.step (program C))
        ⟨some (.headerStart 0), initialState,
          inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))⟩
        (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩)
        (n + q + Q + 6))

theorem headers_budget (q n Q : Nat) (body : List Bool) :
    n + q + Q + 6 ≤ (encodeWords [n, q, Q] ++ body).length + 3 := by
  simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  omega

end UniqueGamesTheorem.Explicit.MachineUniformHeaders

end

end OAI
