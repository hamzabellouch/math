import Mathlib.Tactic.Linarith
import OAI.Computability.PerfectCompleteness.Machines.BinaryNameSearch
import OAI.Computability.PerfectCompleteness.Machines.CanonicalDictionaryAppendMachine
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI


namespace PerfectCompleteness.CanonicalDictionaryMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Token := BinaryNameSearch.Token

def updatedTokens (tokens : List Token) (bits : List Bool) : List Token :=
  tokens ++ [(false, bits)]

theorem stream_append (first second : List Token) :
    BinaryNameSearch.stream (first ++ second) =
      BinaryNameSearch.stream first ++ BinaryNameSearch.stream second := by
  induction first with
  | nil => rfl
  | cons token first ih =>
      simp only [List.cons_append, BinaryNameSearch.stream_cons, ih, List.append_assoc]

theorem stream_updated (tokens : List Token) (bits : List Bool) :
    BinaryNameSearch.stream (updatedTokens tokens bits) =
      BinaryNameSearch.stream tokens ++ (false :: BinaryNameMachine.frame bits) := by
  simp only [updatedTokens, stream_append, BinaryNameSearch.stream_cons,
    BinaryNameSearch.stream_nil, List.append_nil, BinaryNameSearch.tokenBits]

theorem stream_updated_length (tokens : List Token) (bits : List Bool) :
    (BinaryNameSearch.stream (updatedTokens tokens bits)).length =
      (BinaryNameSearch.stream tokens).length + 2 * bits.length + 2 := by
  rw [stream_updated]
  simp only [List.length_append, List.length_cons, BinaryNameMachine.frame_length]
  omega

theorem present (tokens : List Token) (bits : List Bool) :
    bits ∈ BinaryNameSearch.payloads (updatedTokens tokens bits) := by
  apply List.mem_map.mpr
  exact ⟨(false, bits), by simp [updatedTokens], rfl⟩

theorem updated_canonical (tokens : List Token) (bits : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (allCanonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true) :
    ∀ token ∈ updatedTokens tokens bits, BinaryNameMachine.canonical token.2 = true := by
  intro token mem
  rcases List.mem_append.mp mem with old | new
  · exact allCanonical token old
  · have same : token = (false, bits) := by simpa only [List.mem_singleton] using new
    simpa only [same] using canonical

def index (tokens : List Token) (bits : List Bool) : Nat :=
  (BinaryNameSearch.payloads (updatedTokens tokens bits)).idxOf bits

theorem index_le (tokens : List Token) (bits : List Bool) : index tokens bits ≤ tokens.length := by
  have h := List.idxOf_lt_length_of_mem (present tokens bits)
  simpa only [index, BinaryNameSearch.payloads, List.length_map, updatedTokens,
    List.length_append, List.length_singleton, Nat.lt_add_one_iff] using h

theorem suffix_length_le (tokens : List Token) (bits : List Bool) :
    (BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)).length ≤
      (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp [BinaryNameSearch.afterMatch]
  | cons token tokens ih =>
      simp only [BinaryNameSearch.afterMatch, BinaryNameSearch.stream_cons, List.length_append]
      split <;> omega

def steps (tokens : List Token) (bits : List Bool) : Nat :=
  CanonicalDictionaryAppendMachine.steps bits.length (BinaryNameSearch.stream tokens).length +
    2 * ((BinaryNameSearch.stream (updatedTokens tokens bits)).length + 1) + 1 +
    BinaryNameSearch.steps (updatedTokens tokens bits) bits +
    ((BinaryNameSearch.stream (BinaryNameSearch.afterMatch (updatedTokens tokens bits) bits)).length + 1) +
    (index tokens bits + 2)

theorem steps_le (tokens : List Token) (bits : List Bool) :
    steps tokens bits ≤ 3 * (BinaryNameSearch.stream (updatedTokens tokens bits)).length ^ 2 +
      16 * (BinaryNameSearch.stream (updatedTokens tokens bits)).length + 12 := by
  have search := BinaryNameSearch.steps_le_stream (updatedTokens tokens bits) bits
  have suffix := suffix_length_le (updatedTokens tokens bits) bits
  have idx := index_le tokens bits
  have oldCount : tokens.length ≤ (BinaryNameSearch.stream tokens).length := by
    rw [BinaryNameSearch.stream_length]
    omega
  have sizes := stream_updated_length tokens bits
  have keyBound : bits.length ≤ (BinaryNameSearch.stream (updatedTokens tokens bits)).length := by omega
  have product := Nat.mul_le_mul_right (BinaryNameSearch.stream (updatedTokens tokens bits)).length keyBound
  unfold steps CanonicalDictionaryAppendMachine.steps
  nlinarith

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryNameCompare.State A
abbrev clean (ambient : A) : State A := BinaryNameCompare.clean ambient

def appendMap : Fin 5 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 2

def searchMap : Fin 6 → Fin 8
  | 0 => 2
  | 1 => 0
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6

def appendTapes (tape : Fin 8 → K) : Fin 5 → K := fun i => tape (appendMap i)
def searchTapes (tape : Fin 8 → K) : Fin 6 → K := fun i => tape (searchMap i)

omit [DecidableEq K] in
theorem appendTapes_injective (tape : Fin 8 → K) (distinct : Function.Injective tape) :
    Function.Injective (appendTapes tape) :=
  distinct.comp (by decide : Function.Injective appendMap)

omit [DecidableEq K] in
theorem searchTapes_injective (tape : Fin 8 → K) (distinct : Function.Injective tape) :
    Function.Injective (searchTapes tape) :=
  distinct.comp (by decide : Function.Injective searchMap)

inductive Label
  | append (label : CanonicalDictionaryAppendMachine.Label)
  | copyOut
  | copyBack
  | seed
  | search (label : BinaryNameSearch.Label)
  | drain
  | emit
  deriving DecidableEq, Fintype

def main : Label := .append .copyOut

def instruction (tape : Fin 8 → K) (labels : Label → Λ) (done rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .append l => CanonicalDictionaryAppendMachine.instruction (appendTapes tape)
      (fun l => labels (.append l)) (some (labels .copyOut)) l
  | .copyOut => loopAt (tape 1) (tape 5) id false (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 5) (tape 1) (tape 2) false
      (labels .copyBack) (some (labels .seed))
  | .seed => .push (tape 6) (fun _ => false) (.goto fun _ => labels (.search .sign))
  | .search l => BinaryNameSearch.instruction (searchTapes tape)
      (fun l => labels (.search l)) (some (labels .drain)) rejected rejected l
  | .drain => MachineDrain.drain (tape 2) (labels .drain) (some (labels .emit))
  | .emit => loopAt (tape 6) (tape 7) id false (labels .emit) done

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem dictionaryTrace (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
    (base : K → List Bool) (ambient : A) (tokens : List Token) (bits : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (allCanonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (keyWord : base (tape 0) = bits.reverse)
    (dictionaryWord : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 → base (tape i) = []) :
    (advance (TM2.step program))^[steps tokens bits]
      (some ⟨some (labels main), clean ambient, base⟩) =
      some ⟨done, clean ambient,
        Function.update (Function.update base (tape 1)
          (BinaryNameSearch.stream (updatedTokens tokens bits))) (tape 7)
          ((encodeWord (index tokens bits)).reverse ++ base (tape 7))⟩ := by
  have hd (i j : Fin 8) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have he (i : Fin 8) (lo : 2 ≤ i.val := by decide) (hi : i.val ≤ 6 := by decide) :
      base (tape i) = [] := empty i lo hi
  let updated := updatedTokens tokens bits
  let dictionary := BinaryNameSearch.stream updated
  let tail := BinaryNameSearch.stream (BinaryNameSearch.afterMatch updated bits)
  let s₁ := Function.update base (tape 1) dictionary
  let s₂ := Function.update s₁ (tape 2) dictionary
  let s₃ := Function.update s₂ (tape 6) [false]
  let s₄ := tapesAt (tape 2) (tape 6) s₃ tail (encodeWord (index tokens bits))
  let s₅ := Function.update s₄ (tape 2) []
  let s₆ := tapesAt (tape 6) (tape 7) s₅ []
    ((encodeWord (index tokens bits)).reverse ++ s₅ (tape 7))
  have appended := CanonicalDictionaryAppendMachine.appendTrace (appendTapes tape)
    (appendTapes_injective tape distinct) (fun l => labels (.append l))
    (some (labels .copyOut)) program (fun l => atLabels (.append l))
    base bits (BinaryNameSearch.stream tokens) keyWord dictionaryWord
    (he 4) (he 5) (he 2) ambient
  rw [← stream_updated tokens bits] at appended
  change (advance (TM2.step program))^[CanonicalDictionaryAppendMachine.steps
      bits.length (BinaryNameSearch.stream tokens).length]
    (some ⟨some (labels main), clean ambient, base⟩) =
    some ⟨some (labels .copyOut), clean ambient, s₁⟩ at appended
  have s₁dictionary : s₁ (tape 1) = dictionary := by simp [s₁]
  have s₁empty (i : Fin 8) (lo : 2 ≤ i.val) (hi : i.val ≤ 6) : s₁ (tape i) = [] := by
    have ne : i ≠ 1 := by intro h; subst i; omega
    simp [s₁, hd i 1 ne, he i lo hi]
  have copied : (advance (TM2.step program))^[2 * (dictionary.length + 1)]
      (some ⟨some (labels .copyOut), clean ambient, s₁⟩) =
      some ⟨some (labels .seed), clean ambient, s₂⟩ := by
    have h := MachineCopy.copyTrace (tape 1) (tape 2) (tape 5)
      (hd 1 2 (by decide)) (hd 1 5 (by decide)) (hd 2 5 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels .seed)) program
      (atLabels .copyOut) (atLabels .copyBack) s₁ (s₁empty 5 (by decide) (by decide))
      (ambient, false, none) none
    simpa only [s₁dictionary, s₁empty 2 (by decide) (by decide), List.append_nil,
      clean, BinaryNameCompare.clean, s₂] using h
  have s₂counter : s₂ (tape 6) = [] := by
    simp [s₂, hd 6 2 (by decide), s₁empty 6 (by decide) (by decide)]
  have seeded : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seed), clean ambient, s₂⟩) =
      some ⟨some (labels (.search .sign)), clean ambient, s₃⟩ := by
    change some (TM2.stepAux (program (labels .seed)) _ _) = _
    rw [atLabels .seed]
    simp [instruction, TM2.stepAux, s₂counter, s₃]
  have s₃key : s₃ (tape 0) = bits.reverse := by
    simpa [s₃, s₂, s₁, hd 0 6 (by decide), hd 0 2 (by decide), hd 0 1 (by decide)] using keyWord
  have s₃stream : s₃ (tape 2) = dictionary := by simp [s₃, s₂, hd 2 6 (by decide)]
  have s₃counter : s₃ (tape 6) = [false] := by simp [s₃]
  have s₃empty (i : Fin 8) (hi : i = 3 ∨ i = 4 ∨ i = 5) : s₃ (tape i) = [] := by
    rcases hi with rfl | rfl | rfl <;> simp [s₃, s₂, s₁, hd, he]
  have searched : (advance (TM2.step program))^[BinaryNameSearch.steps updated bits]
      (some ⟨some (labels (.search .sign)), clean ambient, s₃⟩) =
      some ⟨some (labels .drain), clean ambient, s₄⟩ := by
    have h := BinaryNameSearch.searchTrace (searchTapes tape) (searchTapes_injective tape distinct)
      (fun l => labels (.search l)) (some (labels .drain)) rejected rejected program
      (fun l => atLabels (.search l)) s₃ ambient updated bits [] [false]
      (updated_canonical tokens bits canonical allCanonical) (present tokens bits) s₃key
      (s₃empty 3 (by simp)) (s₃empty 4 (by simp)) (s₃empty 5 (by simp))
    have initial : tapesAt (tape 2) (tape 6) s₃ dictionary [false] = s₃ := by
      rw [← s₃stream, ← s₃counter]
      exact tapesAt_self _ _ _
    change (advance (TM2.step program))^[BinaryNameSearch.steps updated bits]
      (some ⟨some (labels (.search .sign)), clean ambient,
        tapesAt (tape 2) (tape 6) s₃ (dictionary ++ []) [false]⟩) =
      some ⟨some (labels .drain), clean ambient,
        tapesAt (tape 2) (tape 6) s₃ (tail ++ []) (encodeWord (index tokens bits))⟩ at h
    simpa only [List.append_nil, initial, s₄] using h
  have s₄stream : s₄ (tape 2) = tail := by simp [s₄, hd 2 6 (by decide)]
  have drained : (advance (TM2.step program))^[tail.length + 1]
      (some ⟨some (labels .drain), clean ambient, s₄⟩) =
      some ⟨some (labels .emit), clean ambient, s₅⟩ := by
    have h := MachineDrain.drainTrace (tape 2) (labels .drain) (some (labels .emit)) program
      (atLabels .drain) s₄ tail (ambient, false, none) none
    have initial : Function.update s₄ (tape 2) tail = s₄ := by
      rw [← s₄stream]
      exact Function.update_eq_self _ _
    simpa only [initial, clean, BinaryNameCompare.clean, s₅] using h
  have s₅counter : s₅ (tape 6) = encodeWord (index tokens bits) := by
    simp [s₅, s₄, hd 6 2 (by decide)]
  have emitted : (advance (TM2.step program))^[index tokens bits + 2]
      (some ⟨some (labels .emit), clean ambient, s₅⟩) =
      some ⟨done, clean ambient, s₆⟩ := by
    have h := transferAt_fromTapes (Γ := Alphabet) (σ := A × Bool × Option Bool)
      (tape 6) (tape 7) (hd 6 7 (by decide)) id false (labels .emit) done program
      (atLabels .emit) s₅ (ambient, false, none) none
    change (advance (TM2.step program))^[(s₅ (tape 6)).length + 1]
      (some ⟨some (labels .emit), clean ambient, s₅⟩) =
      some ⟨done, clean ambient, tapesAt (tape 6) (tape 7) s₅ []
        ((s₅ (tape 6)).reverse.map id ++ s₅ (tape 7))⟩ at h
    simpa only [s₅counter, encodeWord_length, List.map_id_fun, id_eq, Nat.add_assoc,
      clean, BinaryNameCompare.clean, s₆] using h
  have restored : s₆ = Function.update (Function.update base (tape 1) dictionary) (tape 7)
      ((encodeWord (index tokens bits)).reverse ++ base (tape 7)) := by
    funext k
    by_cases h7 : k = tape 7
    · subst k
      simp [s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd]
    · by_cases h1 : k = tape 1
      · subst k
        simp [s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd]
      · by_cases h2 : k = tape 2
        · subst k
          simp [s₆, s₅, tapesAt, hd, he 2]
        · by_cases h6 : k = tape 6
          · subst k
            simp [s₆, tapesAt, hd, he 6]
          · simp [s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, h7, h1, h2, h6,
              Function.update_apply]
  have full := joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace appended copied) seeded) searched) drained) emitted
  simpa only [steps, dictionary, updated, tail, restored] using full

def dictionaryInTime (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
    (base : K → List Bool) (ambient : A) (tokens : List Token) (bits : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (allCanonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (keyWord : base (tape 0) = bits.reverse)
    (dictionaryWord : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 → base (tape i) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels main), clean ambient, base⟩
      (some ⟨done, clean ambient,
        Function.update (Function.update base (tape 1)
          (BinaryNameSearch.stream (updatedTokens tokens bits))) (tape 7)
          ((encodeWord (index tokens bits)).reverse ++ base (tape 7))⟩)
      (3 * (BinaryNameSearch.stream (updatedTokens tokens bits)).length ^ 2 +
        16 * (BinaryNameSearch.stream (updatedTokens tokens bits)).length + 12) where
  steps := steps tokens bits
  evals_in_steps := dictionaryTrace tape distinct labels done rejected program atLabels base ambient
    tokens bits canonical allCanonical keyWord dictionaryWord empty
  steps_le_m := steps_le tokens bits

end Program

end PerfectCompleteness.CanonicalDictionaryMachine

end OAI
