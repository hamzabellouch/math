import Mathlib.Tactic.Ring
import OAI.Computability.PerfectCompleteness.Machines.PostfixAlignment
import OAI.Computability.PerfectCompleteness.Machines.PostfixMachine

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixBounds

open StatementCircuit CircuitBatch PostfixModel PostfixMachine PostfixAlignment
open CircuitProducerModel

def RootsBounded (R : Nat) (roots : List Nat) : Prop := ∀ r ∈ roots, r ≤ R

def TokenBounded (R : Nat) : Token → Prop
  | .input wire => wire ≤ R
  | _ => True

theorem fieldSteps_le (tag : Fin 6) (slot : Fin 3) (value R : Nat) (h : value ≤ R) :
    fieldSteps tag slot value ≤ 2 * R + 3 := by
  unfold fieldSteps
  split <;> omega

theorem recordSteps_le (tag : Fin 6) (values : Fin 3 → Nat) (R : Nat)
    (h : ∀ slot, values slot ≤ R) : recordSteps tag values ≤ 6 * R + 10 := by
  have h0 := fieldSteps_le tag 0 (values 0) R (h 0)
  have h1 := fieldSteps_le tag 1 (values 1) R (h 1)
  have h2 := fieldSteps_le tag 2 (values 2) R (h 2)
  unfold recordSteps
  omega

theorem gateRecord_slot_le (current R : Nat) (gate : Gate) (hq : current ≤ R)
    (hg : gate.Bounded (R + 1)) (slot : Fin 3) :
    (gateRecord current gate).slot slot ≤ R := by
  cases gate with
  | const b => cases b <;> fin_cases slot <;> simp [gateRecord, Record.slot] <;> omega
  | not a => fin_cases slot <;> simp [gateRecord, Record.slot] <;> simp [Gate.Bounded] at hg <;> omega
  | and a b => fin_cases slot <;> simp [gateRecord, Record.slot] <;> simp [Gate.Bounded] at hg <;> omega
  | or a b => fin_cases slot <;> simp [gateRecord, Record.slot] <;> simp [Gate.Bounded] at hg <;> omega

theorem operandSteps_le (token : Token) (gate : Gate) (R : Nat)
    (ht : TokenBounded R token) (hg : gate.Bounded (R + 1)) :
    operandSteps token gate ≤ 2 * R + 4 := by
  cases token <;> cases gate <;>
    simp_all [operandSteps, TokenBounded, Gate.Bounded] <;> omega

theorem operandFields_length_le (token : Token) (gate : Gate) (R : Nat)
    (ht : TokenBounded R token) (hg : gate.Bounded (R + 1)) :
    (operandFields token gate).1.length + (operandFields token gate).2.length ≤ 2 * R + 2 := by
  cases token <;> cases gate <;>
    simp_all [operandFields, TokenBounded, Gate.Bounded] <;> omega

theorem tokenSteps_le (current R : Nat) (token : Token) (gate : Gate)
    (hq : current ≤ R) (ht : TokenBounded R token) (hg : gate.Bounded (R + 1)) :
    tokenSteps current token gate ≤ 12 * R + 24 := by
  have ho := operandSteps_le token gate R ht hg
  have hf := operandFields_length_le token gate R ht hg
  have hr := recordSteps_le token.tag (gateRecord current gate).slot R
    (gateRecord_slot_le current R gate hq hg)
  unfold tokenSteps
  omega

theorem takeGate_bounds (token : Token) (roots : List Nat) (gate : Gate) (rest : List Nat)
    (R : Nat) (ht : TokenBounded R token) (hr : RootsBounded R roots)
    (htake : token.takeGate roots = some (gate, rest)) :
    gate.Bounded (R + 1) ∧ RootsBounded R rest := by
  cases token with
  | const b =>
    simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
    rcases htake with ⟨rfl, rfl⟩
    exact ⟨trivial, hr⟩
  | input wire =>
    simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
    rcases htake with ⟨rfl, rfl⟩
    exact ⟨⟨by change wire ≤ R at ht; omega, by change wire ≤ R at ht; omega⟩, hr⟩
  | not =>
    cases roots with
    | nil => simp [Token.takeGate] at htake
    | cons a roots =>
      simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
      rcases htake with ⟨rfl, rfl⟩
      have ha := hr a (by simp)
      exact ⟨by change a < R + 1; omega, fun r h => hr r (by simp [h])⟩
  | and =>
    cases roots with
    | nil => simp [Token.takeGate] at htake
    | cons right roots =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons left roots =>
        simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
        rcases htake with ⟨rfl, rfl⟩
        have hl := hr left (by simp)
        have hr' := hr right (by simp)
        exact ⟨⟨by omega, by omega⟩, fun r h => hr r (by simp [h])⟩
  | or =>
    cases roots with
    | nil => simp [Token.takeGate] at htake
    | cons right roots =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons left roots =>
        simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
        rcases htake with ⟨rfl, rfl⟩
        have hl := hr left (by simp)
        have hr' := hr right (by simp)
        exact ⟨⟨by omega, by omega⟩, fun r h => hr r (by simp [h])⟩

theorem tokensSteps_le (tokens : List Token) (current : Nat) (roots : List Nat) (R : Nat)
    (hq : current + tokens.length ≤ R) (hr : RootsBounded R roots)
    (ht : ∀ token ∈ tokens, TokenBounded R token) :
    tokensSteps current roots tokens ≤ tokens.length * (12 * R + 25) := by
  induction tokens generalizing current roots with
  | nil => simp [tokensSteps]
  | cons token tokens ih =>
    cases htake : token.takeGate roots with
    | none => simp [tokensSteps, htake]
    | some pair =>
      rcases pair with ⟨gate, rest⟩
      have hc : current ≤ R := by simp only [List.length_cons] at hq; omega
      have hb := takeGate_bounds token roots gate rest R (ht token (by simp)) hr htake
      have hs := tokenSteps_le current R token gate hc (ht token (by simp)) hb.1
      have hroots : RootsBounded R (current :: rest) := by
        intro r h
        rcases List.mem_cons.mp h with rfl | h
        · exact hc
        · exact hb.2 r h
      have hi := ih (current + 1) (current :: rest) (by
        simp only [List.length_cons] at hq
        omega) hroots (fun t h => ht t (by simp [h]))
      simp only [tokensSteps, htake, List.length_cons]
      calc
        _ ≤ (1 + (12 * R + 24)) + tokens.length * (12 * R + 25) :=
          Nat.add_le_add (Nat.add_le_add_left hs 1) hi
        _ = _ := by ring

theorem exprTokens_bounded {ι : Type*} (wire : ι → Nat) (e : Expr ι) (R : Nat)
    (hw : ∀ i, wire i ≤ R) : ∀ token ∈ exprTokens wire e, TokenBounded R token := by
  induction e with
  | input i => simp [exprTokens, TokenBounded, hw]
  | const b => simp [exprTokens, TokenBounded]
  | not e ih =>
    intro token ht
    simp only [exprTokens, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact ih token ht
    · trivial
  | and e f ihe ihf =>
    intro token ht
    simp only [exprTokens, List.mem_append, List.mem_singleton, or_assoc] at ht
    rcases ht with ht | ht | rfl
    · exact ihe token ht
    · exact ihf token ht
    · trivial
  | or e f ihe ihf =>
    intro token ht
    simp only [exprTokens, List.mem_append, List.mem_singleton, or_assoc] at ht
    rcases ht with ht | ht | rfl
    · exact ihe token ht
    · exact ihf token ht
    · trivial

theorem forestTokens_bounded {ι : Type*} (wire : ι → Nat) (es : List (Expr ι)) (R : Nat)
    (hw : ∀ i, wire i ≤ R) : ∀ token ∈ forestTokens wire es, TokenBounded R token := by
  intro token ht
  obtain ⟨e, _, he⟩ := List.mem_flatMap.mp ht
  exact exprTokens_bounded wire e R hw token he

theorem forest_tokensSteps_le {ι : Type*} (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (roots : List Nat) (hw : ∀ i, wire i < start)
    (hr : RootsBounded (start + Batch.cost es) roots) :
    tokensSteps start roots (forestTokens wire es) ≤
      Batch.cost es * (12 * (start + Batch.cost es) + 25) := by
  have h := tokensSteps_le (forestTokens wire es) start roots (start + Batch.cost es)
    (by simpa only [forestTokens_length] using Nat.le_refl (start + Batch.cost es)) hr
    (forestTokens_bounded wire es _ (fun i => by have := hw i; omega))
  simpa only [forestTokens_length] using h

theorem forest_recordsBits_length_le {ι : Type*} (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (hw : ∀ i, wire i < start) :
    (recordsBits (gateRecords start (Batch.gates wire start es))).length ≤
      4 * Batch.cost es * (start + Batch.cost es + 5) := by
  have h := encodeWords_length_le
    (recordsWords (gateRecords start (Batch.gates wire start es)))
    (start + (Batch.gates wire start es).length + 4)
    (gateRecords_fields_le start _ (Batch.gates_ordered wire start es hw))
  simpa only [recordsBits, recordsWords_length, gateRecords_length, Batch.gates_length,
    Nat.add_assoc] using h

theorem forest_phases_le {ι : Type*} (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (roots : List Nat) (hw : ∀ i, wire i < start)
    (hr : RootsBounded (start + Batch.cost es) roots) :
    start + (forestTokens wire es).length + 4 +
        tokensSteps start roots (forestTokens wire es) +
        (recordsBits (gateRecords start (Batch.gates wire start es))).length + 3 ≤
      start + Batch.cost es + 7 + Batch.cost es * (16 * (start + Batch.cost es) + 45) := by
  have ht := forest_tokensSteps_le wire es start roots hw hr
  have hg := forest_recordsBits_length_le wire es start hw
  rw [forestTokens_length]
  calc
    _ ≤ start + Batch.cost es + 4 +
        (Batch.cost es * (12 * (start + Batch.cost es) + 25)) +
        (4 * Batch.cost es * (start + Batch.cost es + 5)) + 3 := by omega
    _ = _ := by ring

theorem forest_header_le_input_length {ι : Type*} (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) :
    start + Batch.cost es + 2 ≤ (PostfixModel.inputBits start (forestTokens wire es)).length := by
  rw [forest_inputBits, List.length_append]
  simp only [encodeWords, List.length_append, encodeWord_length, List.length_nil]
  omega

theorem forest_phases_le_input_quadratic {ι : Type*} (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (roots : List Nat) (hw : ∀ i, wire i < start)
    (hr : RootsBounded (start + Batch.cost es) roots) :
    let m := (PostfixModel.inputBits start (forestTokens wire es)).length
    start + (forestTokens wire es).length + 4 +
        tokensSteps start roots (forestTokens wire es) +
        (recordsBits (gateRecords start (Batch.gates wire start es))).length + 3 ≤
      m + 7 + m * (16 * m + 45) := by
  dsimp only
  have hm := forest_header_le_input_length wire es start
  apply (forest_phases_le wire es start roots hw hr).trans
  apply Nat.add_le_add
  · omega
  · apply Nat.mul_le_mul
    · omega
    · omega

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixBounds

end

end OAI
