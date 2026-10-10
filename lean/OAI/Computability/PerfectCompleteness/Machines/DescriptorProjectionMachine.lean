import OAI.Computability.PerfectCompleteness.Reduction.SignedCompletionSchedule
import OAI.Computability.UniqueGames.Machines.MachineFiniteTable

namespace OAI


namespace PerfectCompleteness.DescriptorProjectionMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open SignedCompletionSchedule
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

def projection (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    ProjectionTable q :=
  LocalCompletionSerialization.projection
    (FiniteConstraintMachine.result_correct hq large ⟨descriptor.1, descriptor.2.1⟩)
    descriptor.2.2

theorem projection_apply
    (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large)
    (a : Fin (2 * q)) :
    (projection hq large descriptor).images[a] = descriptorTable hq large descriptor a :=
  (descriptorTable_eq_parsed hq large descriptor.1 descriptor.2 a).symm

def outputWords (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    List Nat := Encoding.tableWords (projection hq large descriptor)

theorem outputWords_eq
    (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    outputWords hq large descriptor =
      List.ofFn (fun a : Fin (2 * q) => (descriptorTable hq large descriptor a).val) :=
  (LocalCompletionSerialization.rawTableWords_eq
    (FiniteConstraintMachine.result_correct hq large ⟨descriptor.1, descriptor.2.1⟩)
    descriptor.2.2).symm

@[simp] theorem outputWords_length
    (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    (outputWords hq large descriptor).length = 2 * q :=
  Encoding.tableWords_length _

def outputBits (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    List Bool := encodeWords (outputWords hq large descriptor)

theorem outputBits_length_le
    (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    (outputBits hq large descriptor).length ≤ (2 * q) * (q + 1) := by
  have hword : ∀ value ∈ outputWords hq large descriptor, value ≤ q := by
    intro value hvalue
    rw [outputWords_eq] at hvalue
    obtain ⟨a, ha⟩ := List.mem_ofFn.mp hvalue
    have hrange := (descriptorTable hq large descriptor a).isLt
    omega
  simpa only [outputBits, outputWords_length] using
    encodeWords_length_le (outputWords hq large descriptor) q hword

theorem outputBits_parse
    (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    decodeWords (outputBits hq large descriptor) >>= Encoding.parseProjection q =
      some (projection hq large descriptor) := by
  rw [outputBits, decodeWords_encodeWords]
  exact Encoding.parseProjection_encoded _


variable {σ : Type} [Fintype σ] [DecidableEq σ]
  (select : σ → Descriptor (rows := rows) (repeats := repeats) hq large)

def keys (σ : Type) [Fintype σ] : List σ := (Finset.univ : Finset σ).toList

omit [DecidableEq σ] in
theorem keys_complete (state : σ) : state ∈ keys σ := by
  simp [keys]

def pushBound : Nat :=
  ((keys σ).map (fun state => (outputBits hq large (select state)).length)).sum

def statement {K Λ : Type} (dst : K) (exit : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ σ :=
  MachineFiniteTable.emit dst (fun state => outputBits hq large (select state)) (keys σ)
    (.goto (fun _ => exit))

theorem statement_trace {K Λ : Type} [DecidableEq K]
    (dst : K) (exit : Λ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (statement hq large select dst exit) state tapes = {
      l := some exit
      var := state
      stk := Function.update tapes dst (outputBits hq large (select state) ++ tapes dst)
    } := by
  rw [statement, MachineFiniteTable.stepAux_emit dst _ (keys σ) (keys_complete)]
  rfl

def emitInTime {K Λ : Type} [DecidableEq K]
    (dst : K) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (label exit : Λ)
    (atLabel : program label = statement hq large select dst exit)
    (state : σ) (tapes : K → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, state, tapes⟩
      (some ⟨some exit, state,
        Function.update tapes dst (outputBits hq large (select state) ++ tapes dst)⟩) 1 :=
  MachineFiniteTable.emitInTime (Γ := fun _ : K => Bool)
    dst (fun state => outputBits hq large (select state))
    (keys σ) keys_complete program label exit
    (by simpa only [statement] using atLabel) state tapes

omit [Fintype σ] [DecidableEq σ] in
theorem output_frame {K : Type} [DecidableEq K]
    (dst : K) (state : σ) (tapes : K → List Bool) (k : K) (hne : k ≠ dst) :
    (Function.update tapes dst (outputBits hq large (select state) ++ tapes dst)) k =
      tapes k :=
  MachineFiniteTable.output_frame dst (fun state => outputBits hq large (select state))
    state tapes k hne

theorem statement_pushBound {K Λ : Type} (dst : K) (exit : Λ) :
    Runtime.statementPushBound (statement hq large select dst exit) ≤
      pushBound hq large select := by
  have h := MachineFiniteTable.emit_push_bound (Γ := fun _ : K => Bool)
    dst (fun state => outputBits hq large (select state)) (keys σ)
    (.goto (fun _ => exit))
  simpa only [statement, pushBound, MachineFiniteTable.tableBound,
    Runtime.statementPushBound, Nat.add_zero] using h

def reverseStatement {K Λ : Type} (dst : K) (exit : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ σ :=
  MachineFiniteTable.emit dst (fun state => (outputBits hq large (select state)).reverse)
    (keys σ) (.goto (fun _ => exit))

theorem reverse_statement_trace {K Λ : Type} [DecidableEq K]
    (dst : K) (exit : Λ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (reverseStatement hq large select dst exit) state tapes = {
      l := some exit
      var := state
      stk := Function.update tapes dst
        ((outputBits hq large (select state)).reverse ++ tapes dst)
    } := by
  rw [reverseStatement, MachineFiniteTable.stepAux_emit dst _ (keys σ) keys_complete]
  rfl

def reverseEmitInTime {K Λ : Type} [DecidableEq K]
    (dst : K) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (label exit : Λ)
    (atLabel : program label = reverseStatement hq large select dst exit)
    (state : σ) (tapes : K → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, state, tapes⟩
      (some ⟨some exit, state,
        Function.update tapes dst
          ((outputBits hq large (select state)).reverse ++ tapes dst)⟩) 1 :=
  MachineFiniteTable.emitInTime (Γ := fun _ : K => Bool) dst
    (fun state => (outputBits hq large (select state)).reverse)
    (keys σ) keys_complete program label exit
    (by simpa only [reverseStatement] using atLabel) state tapes

omit [Fintype σ] [DecidableEq σ] in
theorem reverse_output_frame {K : Type} [DecidableEq K]
    (dst : K) (state : σ) (tapes : K → List Bool) (k : K) (hne : k ≠ dst) :
    (Function.update tapes dst
      ((outputBits hq large (select state)).reverse ++ tapes dst)) k = tapes k :=
  MachineFiniteTable.output_frame dst
    (fun state => (outputBits hq large (select state)).reverse) state tapes k hne

theorem reverse_statement_pushBound {K Λ : Type} (dst : K) (exit : Λ) :
    Runtime.statementPushBound (reverseStatement hq large select dst exit) ≤
      pushBound hq large select := by
  have h := MachineFiniteTable.emit_push_bound (Γ := fun _ : K => Bool)
    dst (fun state => (outputBits hq large (select state)).reverse) (keys σ)
    (.goto (fun _ => exit))
  simpa only [reverseStatement, pushBound, MachineFiniteTable.tableBound,
    List.length_reverse, Runtime.statementPushBound, Nat.add_zero] using h

end
end PerfectCompleteness.DescriptorProjectionMachine

end OAI
