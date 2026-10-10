import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineBinaryTotalInputMachine

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.BinaryLiteralMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryNameCompare.State (A × Bool)
abbrev clean (ambient : A) (sign : Bool := false) : State A :=
  BinaryNameCompare.clean (ambient, sign)

inductive Label
  | readSign | scanKey | copyOut | copyBack
  | search (label : BinaryNameSearch.Label)
  | drainSearch | drainKey | emitIndex | emitSign
  deriving DecidableEq, Fintype

def searchTapes (tape : Fin 9 → K) : Fin 6 → K
  | 0 => tape 3
  | 1 => tape 2
  | 2 => tape 4
  | 3 => tape 5
  | 4 => tape 6
  | 5 => tape 7

omit [DecidableEq K] in
theorem searchTapes_injective (tape : Fin 9 → K) (distinct : Function.Injective tape) :
    Function.Injective (searchTapes tape) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp only [searchTapes] at h
  all_goals first | rfl | have heq := congrArg Fin.val (distinct h); norm_num at heq

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def readSign (tape : Fin 9 → K) (next : Λ) (malformed : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push (tape 7) (fun _ => false)
    (.pop (tape 0) (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.load (fun state => clean state.1.1.1 (state.2.getD false)) (.goto fun _ => next))
        (finish malformed)))

def emitSign (output : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .branch (fun state => state.1.1.2)
    (.push output (fun _ => true) (.push output (fun _ => false) (finish exit)))
    (.push output (fun _ => false) (finish exit))

def instruction (tape : Fin 9 → K) (labels : Label → Λ)
    (exit malformed : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .readSign => readSign tape (labels .scanKey) malformed
  | .scanKey => MachineStateEquiv.statement (BinaryNameCompare.scanStateEquiv (A × Bool))
      (BinaryNameMachine.scan (tape 0) (tape 2) (labels .scanKey)
        (some (labels .copyOut)) malformed)
  | .copyOut => loopAt (tape 1) (tape 6) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 6) (tape 1) (tape 3) false
      (labels .copyBack) (some (labels (.search .sign)))
  | .search l => BinaryNameSearch.instruction (searchTapes tape)
      (fun l => labels (.search l)) (some (labels .drainSearch)) malformed malformed l
  | .drainSearch => MachineDrain.drain (tape 3) (labels .drainSearch)
      (some (labels .drainKey))
  | .drainKey => MachineDrain.drain (tape 2) (labels .drainKey)
      (some (labels .emitIndex))
  | .emitIndex => loopAt (tape 7) (tape 8) id false
      (labels .emitIndex) (some (labels .emitSign))
  | .emitSign => emitSign (tape 8) exit

def signWord (sign : Bool) : List Bool := encodeWord (if sign then 1 else 0)

def index (tokens : List BinaryNameSearch.Token) (bits : List Bool) : Nat :=
  (BinaryNameSearch.payloads tokens).idxOf bits

def outputWord (tokens : List BinaryNameSearch.Token) (bits : List Bool) (sign : Bool) :
    List Bool := encodeWord (index tokens bits) ++ signWord sign

def steps (tokens : List BinaryNameSearch.Token) (bits : List Bool) : Nat :=
  1 + (bits.length + 1) + 2 * ((BinaryNameSearch.stream tokens).length + 1) +
    BinaryNameSearch.steps tokens bits +
    ((BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)).length + 1) +
    (bits.length + 1) + (index tokens bits + 2) + 1

theorem afterMatch_length_le (tokens : List BinaryNameSearch.Token) (bits : List Bool) :
    (BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)).length ≤
      (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp [BinaryNameSearch.afterMatch]
  | cons token tokens ih =>
      simp only [BinaryNameSearch.afterMatch, BinaryNameSearch.stream_cons, List.length_append]
      split <;> omega

theorem steps_le (tokens : List BinaryNameSearch.Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    steps tokens bits ≤
      3 * ((BinaryNameSearch.stream tokens).length + bits.length) ^ 2 +
        13 * ((BinaryNameSearch.stream tokens).length + bits.length) + 9 := by
  have search := BinaryNameSearch.steps_le_stream tokens bits
  have suffix := afterMatch_length_le tokens bits
  have idx : index tokens bits < tokens.length := by
    have h := List.idxOf_lt_length_iff.mpr present
    simpa [index, BinaryNameSearch.payloads] using h
  have count : tokens.length ≤ (BinaryNameSearch.stream tokens).length := by
    rw [BinaryNameSearch.stream_length]
    omega
  unfold steps
  nlinarith [Nat.zero_le ((BinaryNameSearch.stream tokens).length * bits.length)]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1.1.1, base⟩ := by
  cases exit <;> rfl

private theorem joinTrace_inline_MachineBinaryLiteralMachine {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem literalTrace (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit malformed : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit malformed l)
    (base : K → List Bool) (tokens : List BinaryNameSearch.Token)
    (sign : Bool) (bits suffix : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (tokensCanonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (present : bits ∈ BinaryNameSearch.payloads tokens)
    (cursor : base (tape 0) = sign :: (BinaryNameMachine.frame bits ++ suffix))
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 9, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = [])
    (ambient : A) :
    (advance (TM2.step program))^[steps tokens bits]
      (some ⟨some (labels .readSign), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update (Function.update base (tape 0) suffix) (tape 8)
          ((outputWord tokens bits sign).reverse ++ base (tape 8))⟩ := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have he (i : Fin 9) (hlo : 2 ≤ i.val := by decide) (hhi : i.val ≤ 7 := by decide) :
      base (tape i) = [] := empty i hlo hhi
  let s₁ := Function.update (Function.update base (tape 7) [false]) (tape 0)
    (BinaryNameMachine.frame bits ++ suffix)
  let s₂ := Function.update (Function.update s₁ (tape 0) suffix) (tape 2) bits.reverse
  let s₃ := Function.update s₂ (tape 3) (BinaryNameSearch.stream tokens)
  let tail := BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)
  let s₄ := tapesAt (tape 3) (tape 7) s₃ tail (encodeWord (index tokens bits))
  let s₅ := Function.update s₄ (tape 3) []
  let s₆ := Function.update s₅ (tape 2) []
  let s₇ := tapesAt (tape 7) (tape 8) s₆ []
    ((encodeWord (index tokens bits)).reverse ++ s₆ (tape 8))
  let s₈ := Function.update s₇ (tape 8) ((signWord sign).reverse ++ s₇ (tape 8))
  have signRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .readSign), clean ambient, base⟩) =
      some ⟨some (labels .scanKey), clean ambient sign, s₁⟩ := by
    change some (TM2.stepAux (program (labels .readSign)) _ _) = _
    rw [atLabels .readSign]
    simp [instruction, readSign, TM2.stepAux, clean, BinaryNameCompare.clean,
      cursor, he 7, hd 0 7 (by decide), s₁]
  have s₁cursor : s₁ (tape 0) = BinaryNameMachine.frame bits ++ suffix := by simp [s₁]
  have s₁key : s₁ (tape 2) = [] := by
    simp [s₁, hd 2 0 (by decide), hd 2 7 (by decide), he 2]
  have keyRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .scanKey), clean ambient sign, s₁⟩) =
      some ⟨some (labels .copyOut), clean ambient sign, s₂⟩ := by
    let e := BinaryNameCompare.scanStateEquiv (A × Bool)
    let back := MachineStateEquiv.program e.symm program
    have atScan : back (labels .scanKey) =
        BinaryNameMachine.scan (tape 0) (tape 2) (labels .scanKey)
          (some (labels .copyOut)) malformed := by
      change MachineStateEquiv.statement e.symm (program (labels .scanKey)) = _
      rw [atLabels .scanKey]
      exact MachineStateEquiv.statement_symm_statement e _
    have backForward : MachineStateEquiv.program e back = program := by
      funext l
      change MachineStateEquiv.statement e (MachineStateEquiv.statement e.symm (program l)) = _
      exact MachineStateEquiv.statement_symm_statement e.symm _
    have initial : tapesAt (tape 0) (tape 2) s₁
        (BinaryNameMachine.frame bits ++ suffix) [] = s₁ := by
      rw [← s₁cursor, ← s₁key]
      exact tapesAt_self _ _ _
    have native := BinaryNameMachine.framedTrace (tape 0) (tape 2) (hd 0 2 (by decide))
      (labels .scanKey) (some (labels .copyOut)) malformed back atScan s₁
      ((ambient, sign), false) bits suffix [] none
    simp only [canonical, ↓reduceIte, initial, List.append_nil] at native
    have transported := MachineStateEquiv.trace e back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, e, BinaryNameCompare.scanStateEquiv, Equiv.coe_fn_mk,
      BinaryNameMachine.clean, clean, BinaryNameCompare.clean, s₂, tapesAt] using transported
  have s₂permanent : s₂ (tape 1) = BinaryNameSearch.stream tokens := by
    simpa [s₂, s₁, hd 1 0 (by decide), hd 1 2 (by decide), hd 1 7 (by decide)] using permanent
  have s₂empty (i : Fin 9) (hi : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) : s₂ (tape i) = [] := by
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [s₂, s₁, hd, he]
  have copyRun : (advance (TM2.step program))^[2 * ((BinaryNameSearch.stream tokens).length + 1)]
      (some ⟨some (labels .copyOut), clean ambient sign, s₂⟩) =
      some ⟨some (labels (.search .sign)), clean ambient sign, s₃⟩ := by
    have h := MachineCopy.copyTrace (tape 1) (tape 3) (tape 6)
      (hd 1 3 (by decide)) (hd 1 6 (by decide)) (hd 3 6 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels (.search .sign))) program
      (atLabels .copyOut) (atLabels .copyBack) s₂
      (s₂empty 6 (by simp)) ((ambient, sign), false, none) none
    simpa only [s₂permanent, s₂empty 3 (by simp), List.append_nil,
      clean, BinaryNameCompare.clean, s₃] using h
  have s₃key : s₃ (tape 2) = bits.reverse := by
    simp [s₃, s₂, hd 2 3 (by decide)]
  have s₃counter : s₃ (tape 7) = [false] := by
    simp [s₃, s₂, s₁, hd 7 3 (by decide), hd 7 2 (by decide), hd 7 0 (by decide)]
  have s₃stream : s₃ (tape 3) = BinaryNameSearch.stream tokens := by simp [s₃]
  have searchRun : (advance (TM2.step program))^[BinaryNameSearch.steps tokens bits]
      (some ⟨some (labels (.search .sign)), clean ambient sign, s₃⟩) =
      some ⟨some (labels .drainSearch), clean ambient sign, s₄⟩ := by
    have h := BinaryNameSearch.searchTrace (searchTapes tape)
      (searchTapes_injective tape distinct) (fun l => labels (.search l))
      (some (labels .drainSearch)) malformed malformed program
      (fun l => atLabels (.search l)) s₃ (ambient, sign) tokens bits [] [false]
      tokensCanonical present s₃key
      (by simpa [s₃, searchTapes, hd 4 3 (by decide)] using s₂empty 4 (by simp))
      (by simpa [s₃, searchTapes, hd 5 3 (by decide)] using s₂empty 5 (by simp))
      (by simpa [s₃, searchTapes, hd 6 3 (by decide)] using s₂empty 6 (by simp))
    have initial : tapesAt (tape 3) (tape 7) s₃ (BinaryNameSearch.stream tokens) [false] = s₃ := by
      rw [← s₃stream, ← s₃counter]
      exact tapesAt_self _ _ _
    simpa only [searchTapes, List.append_nil, initial, clean, BinaryNameSearch.clean,
      s₄, tail, encodeWord, index] using h
  have s₄stream : s₄ (tape 3) = tail := by simp [s₄, hd 3 7 (by decide)]
  have drainSearchRun : (advance (TM2.step program))^[tail.length + 1]
      (some ⟨some (labels .drainSearch), clean ambient sign, s₄⟩) =
      some ⟨some (labels .drainKey), clean ambient sign, s₅⟩ := by
    have h := MachineDrain.drainTrace (tape 3) (labels .drainSearch)
      (some (labels .drainKey)) program (atLabels .drainSearch) s₄ tail
      ((ambient, sign), false, none) none
    have initial : Function.update s₄ (tape 3) tail = s₄ := by
      rw [← s₄stream]; exact Function.update_eq_self _ _
    simpa only [initial, clean, BinaryNameCompare.clean, s₅] using h
  have s₅key : s₅ (tape 2) = bits.reverse := by
    simp [s₅, s₄, tapesAt, hd 2 3 (by decide), hd 2 7 (by decide), s₃key]
  have drainKeyRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .drainKey), clean ambient sign, s₅⟩) =
      some ⟨some (labels .emitIndex), clean ambient sign, s₆⟩ := by
    have h := MachineDrain.drainTrace (tape 2) (labels .drainKey)
      (some (labels .emitIndex)) program (atLabels .drainKey) s₅ bits.reverse
      ((ambient, sign), false, none) none
    have initial : Function.update s₅ (tape 2) bits.reverse = s₅ := by
      rw [← s₅key]; exact Function.update_eq_self _ _
    simpa only [initial, List.length_reverse, clean, BinaryNameCompare.clean, s₆] using h
  have s₆index : s₆ (tape 7) = encodeWord (index tokens bits) := by
    simp [s₆, s₅, s₄, hd 7 2 (by decide), hd 7 3 (by decide)]
  have indexRun : (advance (TM2.step program))^[index tokens bits + 2]
      (some ⟨some (labels .emitIndex), clean ambient sign, s₆⟩) =
      some ⟨some (labels .emitSign), clean ambient sign, s₇⟩ := by
    change (nextAt (Γ := Alphabet) (tape 8) program)^[index tokens bits + 2]
      (some ⟨some (labels .emitIndex), (((ambient, sign), false, none), none), s₆⟩) =
      some ⟨some (labels .emitSign), (((ambient, sign), false, none), none), s₇⟩
    have h := transferAt_fromTapes (Γ := Alphabet) (tape 7) (tape 8)
      (hd 7 8 (by decide)) id false (labels .emitIndex) (some (labels .emitSign)) program
      (atLabels .emitIndex) s₆ ((ambient, sign), false, none) none
    have time : index tokens bits + 1 + 1 = index tokens bits + 2 := by omega
    simpa only [s₆index, encodeWord_length, List.map_id_fun, id_eq, time, s₇] using h
  have emitRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .emitSign), clean ambient sign, s₇⟩) =
      some ⟨exit, clean ambient, s₈⟩ := by
    change some (TM2.stepAux (program (labels .emitSign)) _ _) = _
    rw [atLabels .emitSign]
    cases sign <;> simp [instruction, emitSign, clean, BinaryNameCompare.clean,
      TM2.stepAux, signWord, encodeWord, s₈, Function.update_idem]
  have full := joinTrace_inline_MachineBinaryLiteralMachine (joinTrace_inline_MachineBinaryLiteralMachine (joinTrace_inline_MachineBinaryLiteralMachine (joinTrace_inline_MachineBinaryLiteralMachine (joinTrace_inline_MachineBinaryLiteralMachine (joinTrace_inline_MachineBinaryLiteralMachine
    (joinTrace_inline_MachineBinaryLiteralMachine signRun keyRun) copyRun) searchRun) drainSearchRun) drainKeyRun) indexRun) emitRun
  have finalTapes : s₈ = Function.update (Function.update base (tape 0) suffix) (tape 8)
      ((outputWord tokens bits sign).reverse ++ base (tape 8)) := by
    funext k
    by_cases h8 : k = tape 8
    · subst k
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, outputWord,
        List.reverse_append, List.append_assoc, hd]
    · by_cases h0 : k = tape 0
      · subst k
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd]
      · by_cases h2 : k = tape 2
        · subst k
          simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 2]
        · by_cases h3 : k = tape 3
          · subst k
            simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 3]
          · by_cases h7 : k = tape 7
            · subst k
              simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 7]
            · simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, h8, h0, h2, h3, h7]
  simpa only [steps, tail, finalTapes] using full

def literalInTime (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit malformed : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit malformed l)
    (base : K → List Bool) (tokens : List BinaryNameSearch.Token)
    (sign : Bool) (bits suffix : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (tokensCanonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (present : bits ∈ BinaryNameSearch.payloads tokens)
    (cursor : base (tape 0) = sign :: (BinaryNameMachine.frame bits ++ suffix))
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 9, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = [])
    (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .readSign), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update (Function.update base (tape 0) suffix) (tape 8)
          ((outputWord tokens bits sign).reverse ++ base (tape 8))⟩)
      (3 * ((BinaryNameSearch.stream tokens).length + bits.length) ^ 2 +
        13 * ((BinaryNameSearch.stream tokens).length + bits.length) + 9) where
  steps := steps tokens bits
  evals_in_steps := literalTrace tape distinct labels exit malformed program atLabels base
    tokens sign bits suffix canonical tokensCanonical present cursor permanent empty ambient
  steps_le_m := steps_le tokens bits present

end DFVSGames.BinaryLiteralMachine

end

section

namespace DFVSGames.BinaryRenameLoop

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

abbrev Token := BinaryNameSearch.Token

def nextSlot (slot : Fin 3) : Fin 3 := if slot = 0 then 1 else if slot = 1 then 2 else 0

def clauseIncrement (slot : Fin 3) : Nat := if slot = 2 then 1 else 0

def finalSlot : Nat → Fin 3 → Fin 3
  | 0, slot => slot
  | n + 1, slot => finalSlot n (nextSlot slot)

def completedClauses : Nat → Fin 3 → Nat
  | 0, _ => 0
  | n + 1, slot => completedClauses n (nextSlot slot) + clauseIncrement slot

theorem finalSlot_three (n : Nat) : finalSlot (n + 3) 0 = finalSlot n 0 := by
  simp [finalSlot, nextSlot]

theorem completedClauses_three (n : Nat) :
    completedClauses (n + 3) 0 = completedClauses n 0 + 1 := by
  simp [completedClauses, nextSlot, clauseIncrement]

@[simp] theorem finalSlot_triples (n : Nat) : finalSlot (3 * n) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, finalSlot_three, ih]

@[simp] theorem completedClauses_triples (n : Nat) : completedClauses (3 * n) 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, completedClauses_three, ih]

def outputBody (tokens input : List Token) : List Bool :=
  input.flatMap (fun token => BinaryLiteralMachine.outputWord tokens token.2 token.1)

@[simp] theorem outputBody_nil (tokens : List Token) : outputBody tokens [] = [] := rfl

@[simp] theorem outputBody_cons (tokens : List Token) (token : Token) (input : List Token) :
    outputBody tokens (token :: input) =
      BinaryLiteralMachine.outputWord tokens token.2 token.1 ++ outputBody tokens input := rfl

def steps (tokens : List Token) : List Token → Nat
  | [] => 1
  | token :: input => BinaryLiteralMachine.steps tokens token.2 + 2 + steps tokens input

theorem payload_length_le_stream (tokens : List Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    bits.length ≤ (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp at present
  | cons token tokens ih =>
      rcases List.mem_cons.mp present with equal | remaining
      · rw [equal]
        simp only [BinaryNameSearch.stream_cons, List.length_append,
          BinaryNameSearch.tokenBits, List.length_cons, BinaryNameMachine.frame_length]
        omega
      · have tail := ih remaining
        simp only [BinaryNameSearch.stream_cons, List.length_append]
        omega

def perLiteralBound (streamLength : Nat) : Nat :=
  12 * streamLength ^ 2 + 26 * streamLength + 11

theorem literal_steps_le (tokens : List Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    BinaryLiteralMachine.steps tokens bits + 2 ≤
      perLiteralBound (BinaryNameSearch.stream tokens).length := by
  have body := BinaryLiteralMachine.steps_le tokens bits present
  have size := payload_length_le_stream tokens bits present
  have sumBound : (BinaryNameSearch.stream tokens).length + bits.length ≤
      2 * (BinaryNameSearch.stream tokens).length := by omega
  have sq := Nat.mul_self_le_mul_self sumBound
  unfold perLiteralBound
  nlinarith

theorem steps_le (tokens input : List Token) (included : ∀ token ∈ input, token ∈ tokens) :
    steps tokens input ≤
      perLiteralBound (BinaryNameSearch.stream tokens).length * input.length + 1 := by
  induction input with
  | nil => simp [steps]
  | cons token input ih =>
      have present : token.2 ∈ BinaryNameSearch.payloads tokens :=
        List.mem_map.mpr ⟨token, included token (by simp), rfl⟩
      have head := literal_steps_le tokens token.2 present
      have tail := ih (fun t ht => included t (by simp [ht]))
      simp only [steps, List.length_cons]
      nlinarith

theorem steps_le_cubic (tokens input : List Token)
    (included : ∀ token ∈ input, token ∈ tokens)
    (countBound : input.length ≤ (BinaryNameSearch.stream tokens).length) :
    steps tokens input ≤
      12 * (BinaryNameSearch.stream tokens).length ^ 3 +
      26 * (BinaryNameSearch.stream tokens).length ^ 2 +
      11 * (BinaryNameSearch.stream tokens).length + 1 := by
  calc
    steps tokens input ≤
        perLiteralBound (BinaryNameSearch.stream tokens).length * input.length + 1 :=
      steps_le tokens input included
    _ ≤ perLiteralBound (BinaryNameSearch.stream tokens).length *
        (BinaryNameSearch.stream tokens).length + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ countBound) _
    _ = _ := by unfold perLiteralBound; ring

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryLiteralMachine.State (A × Fin 3)
abbrev clean (ambient : A) (slot : Fin 3) : State A :=
  BinaryLiteralMachine.clean (ambient, slot)

inductive Label
  | entry
  | literal (label : BinaryLiteralMachine.Label)
  | tally
  deriving DecidableEq, Fintype

def literalTapes (tape : Fin 11 → K) : Fin 9 → K := fun i => tape i.castSucc.castSucc

omit [DecidableEq K] in
theorem literalTapes_injective (tape : Fin 11 → K) (distinct : Function.Injective tape) :
    Function.Injective (literalTapes tape) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 11 => i.val) (distinct h)

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1.1 state.1.1.1.2)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def next (again : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1.1 (nextSlot state.1.1.1.2))
    (.goto fun _ => again)

def instruction (tape : Fin 11 → K) (labels : Label → Λ)
    (done malformed : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .entry =>
      .pop (tape 0) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.push (tape 0) (fun state => state.2.getD false)
            (finish (some (labels (.literal .readSign)))))
          (finish done))
  | .literal l => BinaryLiteralMachine.instruction (literalTapes tape)
      (fun l => labels (.literal l)) (some (labels .tally)) malformed l
  | .tally =>
      .push (tape 9) (fun _ => true)
        (.branch (fun state => state.1.1.1.2 == (2 : Fin 3))
          (.push (tape 10) (fun _ => true) (next (labels .entry)))
          (next (labels .entry)))

def loopTapes (tape : Fin 11 → K) (base : K → List Bool)
    (cursor output variableCounter clauses : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (tape 0) cursor) (tape 8) output) (tape 9) variableCounter) (tape 10) clauses

theorem loopTapes_cursor (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 0) = cursor := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_output (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 8) = output := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_variables (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 9) = variableCounter := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_clauses (tape : Fin 11 → K)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 10) = clauses := by
  simp [loopTapes]

private theorem update_cursor_inline_MachineBinaryRenameLoop (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 0) replacement =
      loopTapes tape base replacement output variableCounter clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 0
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

private theorem update_output_inline_MachineBinaryRenameLoop (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 8) replacement =
      loopTapes tape base cursor replacement variableCounter clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 8
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

private theorem update_variables_inline_MachineBinaryRenameLoop (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 9) replacement =
      loopTapes tape base cursor output replacement clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 9
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

private theorem update_clauses_inline_MachineBinaryRenameLoop (tape : Fin 11 → K)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 10) replacement =
      loopTapes tape base cursor output variableCounter replacement := by
  simp [loopTapes]

theorem loopTapes_other (tape : Fin 11 → K) (base : K → List Bool)
    (cursor output variableCounter clauses : List Bool) (k : K)
    (h0 : k ≠ tape 0) (h8 : k ≠ tape 8) (h9 : k ≠ tape 9) (h10 : k ≠ tape 10) :
    loopTapes tape base cursor output variableCounter clauses k = base k := by
  simp [loopTapes, h0, h8, h9, h10]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base =
      ⟨exit, clean state.1.1.1.1 state.1.1.1.2, base⟩ := by
  cases exit <;> rfl

private theorem joinTrace_inline_MachineBinaryRenameLoop {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

variable (tape : Fin 11 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done malformed : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done malformed l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem peekStep (slot : Fin 3) (head : Bool) (tail output variableCounter clauses : List Bool) :
    TM2.step program
      ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base (head :: tail) output variableCounter clauses⟩ =
      some ⟨some (labels (.literal .readSign)), clean ambient slot,
        loopTapes tape base (head :: tail) output variableCounter clauses⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change some (TM2.stepAux (program (labels .entry)) _ _) = _
  rw [atLabels .entry]
  simp [instruction, TM2.stepAux, clean, BinaryLiteralMachine.clean, BinaryNameCompare.clean,
    loopTapes_cursor tape distinct, update_cursor_inline_MachineBinaryRenameLoop tape distinct]

theorem emptyStep (slot : Fin 3) (output variableCounter clauses : List Bool) :
    TM2.step program
      ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base [] output variableCounter clauses⟩ =
      some ⟨done, clean ambient slot, loopTapes tape base [] output variableCounter clauses⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change some (TM2.stepAux (program (labels .entry)) _ _) = _
  rw [atLabels .entry]
  simp [instruction, TM2.stepAux, clean, BinaryLiteralMachine.clean, BinaryNameCompare.clean,
    loopTapes_cursor tape distinct, update_cursor_inline_MachineBinaryRenameLoop tape distinct]

theorem tallyStep (slot : Fin 3) (cursor output variableCounter clauses : List Bool) :
    TM2.step program
      ⟨some (labels .tally), clean ambient slot,
        loopTapes tape base cursor output variableCounter clauses⟩ =
      some ⟨some (labels .entry), clean ambient (nextSlot slot),
        loopTapes tape base cursor output (true :: variableCounter)
          (List.replicate (clauseIncrement slot) true ++ clauses)⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change some (TM2.stepAux (program (labels .tally)) _ _) = _
  rw [atLabels .tally]
  fin_cases slot <;>
    simp [instruction, TM2.stepAux, clean, BinaryLiteralMachine.clean, BinaryNameCompare.clean,
      next, nextSlot, clauseIncrement, loopTapes_variables tape distinct, loopTapes_clauses,
      update_variables_inline_MachineBinaryRenameLoop tape distinct, update_clauses_inline_MachineBinaryRenameLoop]

theorem bodyTrace (tokens : List Token) (token : Token) (slot : Fin 3)
    (suffix output variableCounter clauses : List Bool)
    (canonical : BinaryNameMachine.canonical token.2 = true)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (present : token.2 ∈ BinaryNameSearch.payloads tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[BinaryLiteralMachine.steps tokens token.2 + 2]
      (some ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix) output variableCounter clauses⟩) =
      some ⟨some (labels .entry), clean ambient (nextSlot slot),
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let initial := loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix)
    output variableCounter clauses
  have first : (advance (TM2.step program))^[1]
      (some ⟨some (labels .entry), clean ambient slot, initial⟩) =
      some ⟨some (labels (.literal .readSign)), clean ambient slot, initial⟩ := by
    simpa only [Function.iterate_one, advance_some, initial,
      BinaryNameSearch.tokenBits, List.cons_append] using
      peekStep tape distinct labels done malformed program atLabels base ambient slot token.1
        (BinaryNameMachine.frame token.2 ++ suffix) output variableCounter clauses
  have workEmpty (i : Fin 11) (lo : 2 ≤ i.val) (hi : i.val ≤ 7) :
      initial (tape i) = [] := by
    have h0 : i ≠ 0 := by intro h; subst i; omega
    have h8 : i ≠ 8 := by intro h; subst i; omega
    have h9 : i ≠ 9 := by intro h; subst i; omega
    have h10 : i ≠ 10 := by intro h; subst i; omega
    simpa [initial, loopTapes, hd i 0 h0, hd i 8 h8, hd i 9 h9, hd i 10 h10]
      using empty i lo hi
  have literal := BinaryLiteralMachine.literalTrace (literalTapes tape)
    (literalTapes_injective tape distinct) (fun l => labels (.literal l))
    (some (labels .tally)) malformed program (fun l => atLabels (.literal l))
    initial tokens token.1 token.2 suffix canonical tokensCanonical present
    (by simp [initial, literalTapes, loopTapes, BinaryNameSearch.tokenBits, hd])
    (by simpa [initial, literalTapes, loopTapes, hd] using permanent)
    (fun i lo hi => workEmpty i.castSucc.castSucc lo hi) (ambient, slot)
  have finalTapes :
      Function.update (Function.update initial (literalTapes tape 0) suffix)
        (literalTapes tape 8)
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++
          initial (literalTapes tape 8)) =
      loopTapes tape base suffix
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        variableCounter clauses := by
    have out : initial (literalTapes tape 8) = output := by
      simp [initial, literalTapes, loopTapes, hd]
    rw [out]
    change Function.update (Function.update
      (loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix) output variableCounter clauses)
      (tape 0) suffix) (tape 8) _ = _
    rw [update_cursor_inline_MachineBinaryRenameLoop tape distinct, update_output_inline_MachineBinaryRenameLoop tape distinct]
  rw [finalTapes] at literal
  have tally : (advance (TM2.step program))^[1]
      (some ⟨some (labels .tally), clean ambient slot,
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          variableCounter clauses⟩) =
      some ⟨some (labels .entry), clean ambient (nextSlot slot),
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      tallyStep tape distinct labels done malformed program atLabels base ambient slot suffix
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        variableCounter clauses
  have full := joinTrace_inline_MachineBinaryRenameLoop (joinTrace_inline_MachineBinaryRenameLoop first literal) tally
  simpa only [show 1 + BinaryLiteralMachine.steps tokens token.2 + 1 =
    BinaryLiteralMachine.steps tokens token.2 + 2 by omega] using full

theorem loopTrace (tokens input : List Token) (slot : Fin 3)
    (output variableCounter clauses : List Bool)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (included : ∀ t ∈ input, t ∈ tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[steps tokens input]
      (some ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base (BinaryNameSearch.stream input) output variableCounter clauses⟩) =
      some ⟨done, clean ambient (finalSlot input.length slot),
        loopTapes tape base [] ((outputBody tokens input).reverse ++ output)
          (List.replicate input.length true ++ variableCounter)
          (List.replicate (completedClauses input.length slot) true ++ clauses)⟩ := by
  induction input generalizing slot output variableCounter clauses with
  | nil =>
      simpa only [steps, Function.iterate_one, advance_some, BinaryNameSearch.stream_nil,
        List.length_nil, outputBody_nil, List.reverse_nil, List.nil_append,
        finalSlot, completedClauses, List.replicate_zero] using
        emptyStep tape distinct labels done malformed program atLabels base ambient
          slot output variableCounter clauses
  | cons token input ih =>
      have member := included token (by simp)
      have present : token.2 ∈ BinaryNameSearch.payloads tokens :=
        List.mem_map.mpr ⟨token, member, rfl⟩
      have first := bodyTrace tape distinct labels done malformed program atLabels base ambient
        tokens token slot (BinaryNameSearch.stream input) output variableCounter clauses
        (tokensCanonical token member) tokensCanonical present permanent empty
      have rest := ih (nextSlot slot)
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)
        (fun t ht => included t (by simp [ht]))
      have full := joinTrace_inline_MachineBinaryRenameLoop first rest
      have variableEq : List.replicate input.length true ++ (true :: variableCounter) =
          List.replicate (input.length + 1) true ++ variableCounter := by
        rw [List.replicate_succ']
        simp only [List.append_assoc, List.singleton_append]
      have clauseEq : List.replicate (completedClauses input.length (nextSlot slot)) true ++
          (List.replicate (clauseIncrement slot) true ++ clauses) =
          List.replicate (completedClauses (input.length + 1) slot) true ++ clauses := by
        rw [← List.append_assoc, ← List.replicate_add]
        rfl
      simpa only [steps, BinaryNameSearch.stream_cons, List.length_cons, finalSlot,
        outputBody_cons, List.reverse_append, List.append_assoc, variableEq, clauseEq] using full

theorem triplesTrace (tokens input : List Token) (count : Nat)
    (length_eq : input.length = 3 * count) (output variableCounter clauses : List Bool)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (included : ∀ t ∈ input, t ∈ tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[steps tokens input]
      (some ⟨some (labels .entry), clean ambient 0,
        loopTapes tape base (BinaryNameSearch.stream input) output variableCounter clauses⟩) =
      some ⟨done, clean ambient 0,
        loopTapes tape base [] ((outputBody tokens input).reverse ++ output)
          (List.replicate (3 * count) true ++ variableCounter)
          (List.replicate count true ++ clauses)⟩ := by
  have h := loopTrace tape distinct labels done malformed program atLabels base ambient
    tokens input 0 output variableCounter clauses tokensCanonical included permanent empty
  simpa only [length_eq, finalSlot_triples, completedClauses_triples] using h

def triplesInTime (tokens input : List Token) (count : Nat)
    (length_eq : input.length = 3 * count) (output variableCounter clauses : List Bool)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (included : ∀ t ∈ input, t ∈ tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .entry), clean ambient 0,
        loopTapes tape base (BinaryNameSearch.stream input) output variableCounter clauses⟩
      (some ⟨done, clean ambient 0,
        loopTapes tape base [] ((outputBody tokens input).reverse ++ output)
          (List.replicate (3 * count) true ++ variableCounter)
          (List.replicate count true ++ clauses)⟩)
      (perLiteralBound (BinaryNameSearch.stream tokens).length * input.length + 1) where
  steps := steps tokens input
  evals_in_steps := triplesTrace tape distinct labels done malformed program atLabels base ambient
    tokens input count length_eq output variableCounter clauses tokensCanonical included permanent empty
  steps_le_m := steps_le tokens input included

end Program

end DFVSGames.BinaryRenameLoop

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
