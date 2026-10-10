import Mathlib.Data.List.OfFn
import OAI.Computability.PerfectCompleteness.Construction.LocalCompletionFamily
import OAI.Computability.PerfectCompleteness.Decoding.Projection
import OAI.Computability.PerfectCompleteness.Machines.EncodingLemmas
import OAI.Computability.PerfectCompleteness.Machines.FiniteBlockMachineLemmas

namespace OAI


namespace PerfectCompleteness.LocalCompletionMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open LocalCompletionFamily MachineFixedBlockMap

noncomputable section

def inputEnum (q : Nat) : Input q ≃ Fin (Fintype.card (Input q)) :=
  Fintype.equivFin (Input q)

def resultEnum (q : Nat) : Result q ≃ Fin (Fintype.card (Result q)) :=
  Fintype.equivFin (Result q)

def inputBits {q : Nat} (input : Input q) : List Bool :=
  FiniteBlockMachine.word (inputEnum q) input

def resultBits {q : Nat} (result : Result q) : List Bool :=
  FiniteBlockMachine.word (resultEnum q) result

@[simp] theorem inputBits_length {q : Nat} (input : Input q) :
    (inputBits input).length = Fintype.card (Input q) :=
  FiniteBlockMachine.word_length (inputEnum q) input

@[simp] theorem resultBits_length {q : Nat} (result : Result q) :
    (resultBits result).length = Fintype.card (Result q) :=
  FiniteBlockMachine.word_length (resultEnum q) result

theorem resultBits_injective (q : Nat) : Function.Injective (resultBits (q := q)) := by
  intro a b h
  exact FiniteBlockMachine.encode_injective (resultEnum q) (List.ofFn_injective h)

def defaultInput {q : Nat} (hq : 0 < q) : Input q :=
  (fun _ => false, fun _ => ⟨0, hq⟩)

def computation {q : Nat} (hq : 0 < q) :
    TM2ComputableInPolyTime (inputBits (q := q)) resultBits (lookup hq) :=
  FiniteBlockMachine.computation (inputEnum q) (resultEnum q) (defaultInput hq) (lookup hq)

theorem workAlphabet_finite {q : Nat} (hq : 0 < q) (k : (computation hq).tm.K) :
    Finite ((computation hq).tm.Γ k) := by
  change Finite Bool
  infer_instance

theorem exact_pushBound {q : Nat} (hq : 0 < q) :
    Runtime.statementPushBound ((computation hq).tm.m ()) = Fintype.card (Result q) :=
  FiniteBlockMachine.machine_pushBound (inputEnum q) (resultEnum q) (defaultInput hq) (lookup hq)

theorem produces_correct_result {q : Nat} (hq : 0 < q) (input : Input q)
    (hadmissible : Admissible input) :
    ∃ result : Result q, Correct input result ∧
      Nonempty (TM2OutputsInTime (computation hq).tm
        (inputBits input) (some (resultBits result)) 1) := by
  refine ⟨lookup hq input, lookup_correct hq input hadmissible, ⟨?_⟩⟩
  have h := (computation hq).outputsFun input
  change TM2OutputsInTime (computation hq).tm ((inputBits input).map id)
    (some ((resultBits (lookup hq input)).map id))
      ((1 : Polynomial Nat).eval (inputBits input).length) at h
  rw [Polynomial.eval_one] at h
  exact Eq.mp (congrArg₂
    (fun (i o : List Bool) => TM2OutputsInTime (computation hq).tm i (some o) 1)
    (List.map_id (inputBits input)) (List.map_id (resultBits (lookup hq input)))) h

theorem statement_trace {K Λ A : Type} [DecidableEq K] {q : Nat}
    (hq : 0 < q) (src dst : K) (exit : Option Λ) (hne : src ≠ dst)
    (input : Input q) (suffix : List Bool)
    (state : A × Buffer (Fintype.card (Input q))) (tapes : K → List Bool)
    (hinput : tapes src = inputBits input ++ suffix) :
    TM2.stepAux
        (FiniteBlockMachine.statement src dst exit (inputEnum q) (resultEnum q)
          (defaultInput hq) (lookup hq)) state tapes =
      { l := exit, var := (state.1, emptyBuffer (Fintype.card (Input q))),
        stk := Function.update (Function.update tapes src suffix) dst
          (resultBits (lookup hq input) ++ tapes dst) } :=
  FiniteBlockMachine.statement_trace src dst exit hne (inputEnum q) (resultEnum q)
    (defaultInput hq) input (lookup hq) suffix state tapes hinput

end
end PerfectCompleteness.LocalCompletionMachine


namespace PerfectCompleteness.LocalCompletionSerialization

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open LocalCompletionFamily LocalCompletionMachine

noncomputable section

def rawTableWords {q : Nat} (result : Result q) (seed : Fin (activeCount result)) :
    List Nat := List.ofFn (fun a : Fin (2 * q) => (table result seed a).val)

@[simp] theorem rawTableWords_length {q : Nat} (result : Result q)
    (seed : Fin (activeCount result)) :
    (rawTableWords result seed).length = 2 * q := List.length_ofFn

def payloadWords {q : Nat} (result : Result q) : List Nat :=
  activeCount result :: (List.finRange (activeCount result)).flatMap (rawTableWords result)

def payloadBits {q : Nat} (result : Result q) : List Bool :=
  encodeWords (payloadWords result)

theorem payloadWords_length {q : Nat} (result : Result q) :
    (payloadWords result).length = 1 + activeCount result * (2 * q) := by
  have hlen (seeds : List (Fin (activeCount result))) :
      (seeds.flatMap (rawTableWords result)).length = seeds.length * (2 * q) := by
    induction seeds with
    | nil => simp
    | cons seed seeds ih =>
      simp only [List.flatMap_cons, List.length_append, rawTableWords_length,
        List.length_cons, ih, Nat.add_mul, Nat.one_mul]
      omega
  simp only [payloadWords, List.length_cons, hlen, List.length_finRange]
  omega

theorem payloadBits_length_le {q : Nat} (result : Result q) :
    (payloadBits result).length ≤ (1 + (2 * q) * (2 * q)) * (2 * q + 1) := by
  have hword : ∀ n ∈ payloadWords result, n ≤ 2 * q := by
    intro n hn
    rcases List.mem_cons.mp hn with h | h
    · simpa only [h] using activeCount_le result
    · obtain ⟨seed, _, hseed⟩ := List.mem_flatMap.mp h
      obtain ⟨a, ha⟩ := List.mem_ofFn.mp hseed
      change (table result seed a).val = n at ha
      have hrange := (table result seed a).isLt
      omega
  exact (encodeWords_length_le (payloadWords result) (2 * q) hword).trans
    (Nat.mul_le_mul_right (2 * q + 1) (by
      rw [payloadWords_length]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right (2 * q) (activeCount_le result)) 1))

@[simp] theorem decode_payloadBits {q : Nat} (result : Result q) :
    decodeWords (payloadBits result) = some (payloadWords result) :=
  decodeWords_encodeWords _

def projection {q : Nat} {input : Input q} {result : Result q}
    (correct : Correct input result) (seed : Fin (activeCount result)) : ProjectionTable q :=
  ProjectionTable.ofMap (table result seed) (by
    intro b
    simpa only [← Nat.card_eq_fintype_card] using correct.exact_two seed b)

@[simp] theorem projection_apply {q : Nat} {input : Input q} {result : Result q}
    (correct : Correct input result) (seed : Fin (activeCount result)) (a : Fin (2 * q)) :
    (projection correct seed).images[a] = table result seed a := by
  exact ProjectionTable.ofMap_apply (table result seed) _ a

theorem rawTableWords_eq {q : Nat} {input : Input q} {result : Result q}
    (correct : Correct input result) (seed : Fin (activeCount result)) :
    rawTableWords result seed = Encoding.tableWords (projection correct seed) := by
  change List.ofFn (fun a => (table result seed a).val) =
    (Vector.ofFn (table result seed)).toList.map Fin.val
  rw [Vector.toList_ofFn, List.map_ofFn]
  rfl

theorem parse_rawTableWords {q : Nat} {input : Input q} {result : Result q}
    (correct : Correct input result) (seed : Fin (activeCount result)) :
    Encoding.parseProjection q (rawTableWords result seed) =
      some (projection correct seed) := by
  rw [rawTableWords_eq correct, Encoding.parseProjection_encoded]

def parseTables (q : Nat) : Nat → List Nat → Option (List (ProjectionTable q) × List Nat)
  | 0, words => some ([], words)
  | n + 1, words => do
      let head ← Encoding.parseProjection q (words.take (2 * q))
      let (tail, rest) ← parseTables q n (words.drop (2 * q))
      return (head :: tail, rest)

theorem parseTables_encoded {q : Nat} (tables : List (ProjectionTable q))
    (rest : List Nat) :
    parseTables q tables.length (tables.flatMap Encoding.tableWords ++ rest) =
      some (tables, rest) := by
  induction tables with
  | nil => rfl
  | cons head tail ih =>
    have taken := List.take_left' (l₂ := tail.flatMap Encoding.tableWords ++ rest)
      (Encoding.tableWords_length head)
    have dropped := List.drop_left' (l₂ := tail.flatMap Encoding.tableWords ++ rest)
      (Encoding.tableWords_length head)
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, parseTables,
      taken, dropped, Encoding.parseProjection_encoded, Option.bind_eq_bind, Option.bind_some, ih]
    rfl

def parsePayload (q : Nat) : List Nat → Option (List (ProjectionTable q))
  | [] => none
  | count :: words => do
      let (tables, rest) ← parseTables q count words
      if rest = [] then some tables else none

theorem parse_payload {q : Nat} {input : Input q} {result : Result q}
    (correct : Correct input result) :
    parsePayload q (payloadWords result) =
      some ((List.finRange (activeCount result)).map (projection correct)) := by
  let seeds := List.finRange (activeCount result)
  have hwords : seeds.flatMap (rawTableWords result) =
      (seeds.map (projection correct)).flatMap Encoding.tableWords := by
    simp only [List.flatMap_map]
    congr 1
    funext seed
    exact rawTableWords_eq correct seed
  have hlen : (seeds.map (projection correct)).length = activeCount result := by
    simp [seeds]
  have hparse := parseTables_encoded (seeds.map (projection correct)) []
  rw [hlen, List.append_nil] at hparse
  change (do
    let (tables, rest) ← parseTables q (activeCount result) (seeds.flatMap (rawTableWords result))
    if rest = [] then some tables else none) = _
  rw [hwords, hparse]
  rfl

def emit {q : Nat} (hq : 0 < q) (input : Input q) : List Bool :=
  payloadBits (lookup hq input)

def computation {q : Nat} (hq : 0 < q) :
    TM2ComputableInPolyTime (inputBits (q := q)) id (emit hq) :=
  FiniteWordMachine.computation (inputEnum q) (defaultInput hq) (emit hq)

def machine_output {q : Nat} (hq : 0 < q) (input : Input q) :
    TM2OutputsInTime (computation hq).tm (inputBits input)
      (some (payloadBits (lookup hq input))) 1 := by
  have h := (computation hq).outputsFun input
  change TM2OutputsInTime (computation hq).tm ((inputBits input).map id)
    (some ((payloadBits (lookup hq input)).map id)) ((1 : Polynomial Nat).eval _) at h
  rw [Polynomial.eval_one] at h
  exact Eq.mp (congrArg₂
    (fun (i o : List Bool) => TM2OutputsInTime (computation hq).tm i (some o) 1)
    (List.map_id (inputBits input)) (List.map_id (payloadBits (lookup hq input)))) h

theorem machine_output_parses {q : Nat} (hq : 0 < q) (input : Input q)
    (hadmissible : Admissible input) :
    ∃ result : Result q, ∃ correct : Correct input result,
      Nonempty (TM2OutputsInTime (computation hq).tm
        (inputBits input) (some (payloadBits result)) 1) ∧
      decodeWords (payloadBits result) >>= parsePayload q =
        some ((List.finRange (activeCount result)).map
          (projection correct)) := by
  refine ⟨lookup hq input, lookup_correct hq input hadmissible, ⟨machine_output hq input⟩, ?_⟩
  rw [decode_payloadBits]
  exact parse_payload (lookup_correct hq input hadmissible)

theorem workAlphabet_finite {q : Nat} (hq : 0 < q) (k : (computation hq).tm.K) :
    Finite ((computation hq).tm.Γ k) := by
  change Finite Bool
  infer_instance

end
end PerfectCompleteness.LocalCompletionSerialization

end OAI
