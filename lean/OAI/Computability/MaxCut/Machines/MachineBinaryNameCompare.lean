import Mathlib
import OAI.Computability.MaxCut.Machines.Runtime2

namespace OAI

/-!
Compare one framed binary name with an already extracted reversed key.
The candidate stream loses precisely that name frame. The key and every other
non-work stack are preserved; the three work stacks are empty again on exit.
The scanner, copy loops, and head-by-head comparison all execute actual TM2
instructions. Whole words occur only in the correctness specification.
-/

namespace MaxCutGames.BinaryNameCompare

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Bool × Option Bool) × Option Bool

def clean (ambient : A) : State A := ((ambient, false, none), none)

def scanStateEquiv (A : Type) : BinaryNameMachine.State (A × Bool) ≃ State A where
  toFun s := ((s.1.1, s.1.2, s.2.1), s.2.2)
  invFun s := ((s.1.1, s.1.2.1), s.1.2.2, s.2)
  left_inv := by rintro ⟨⟨a, b⟩, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

def compareStateEquiv (A : Type) : MachineCompare.State A ≃ State A where
  toFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  invFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

inductive Label
  | scan | copyOut | copyBack | compare
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .copyOut, .copyBack, .compare]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

/-- Tapes: candidate stream, preserved key, candidate payload, key copy, scratch. -/
def instruction (tape : Fin 5 → K) (labels : Label → Λ)
    (equalExit differentExit malformedExit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .scan => MachineStateEquiv.statement (scanStateEquiv A)
      (BinaryNameMachine.scan (tape 0) (tape 2) (labels .scan)
        (some (labels .copyOut)) malformedExit)
  | .copyOut => MaxCutGames.Reduction.MachineTransfer.loopAt (tape 1) (tape 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 4) (tape 1) (tape 3) false
      (labels .copyBack) (some (labels .compare))
  | .compare => MachineStateEquiv.statement (compareStateEquiv A)
      (MachineCompare.loop (tape 2) (tape 3) (labels .compare) equalExit differentExit)

def steps (payloadLength keyLength : Nat) : Nat :=
  (payloadLength + 1) + 2 * (keyLength + 1) + (max payloadLength keyLength + 1)

theorem steps_le (payloadLength keyLength : Nat) :
    steps payloadLength keyLength ≤ 2 * payloadLength + 3 * keyLength + 4 := by
  unfold steps
  omega

private theorem joinTrace_inline_MachineBinaryNameCompare {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

/-- The name is actually scanned, the key actually copied, and the resulting
payloads actually compared. Program premises are literal instruction equations. -/
theorem compareTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (equalExit differentExit malformedExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) =
      instruction tape labels equalExit differentExit malformedExit l)
    (base : K → List Bool) (bits suffix key : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (sourceWord : base (tape 0) = BinaryNameMachine.frame bits ++ suffix)
    (keyWord : base (tape 1) = key)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (ambient : A) :
    (advance (TM2.step program))^[steps bits.length key.length]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, Function.update base (tape 0) suffix⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let finalBase := Function.update base (tape 0) suffix
  let afterScan := Function.update finalBase (tape 2) bits.reverse
  let afterCopy := Function.update afterScan (tape 3) key
  have scanRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨some (labels .copyOut), clean ambient, afterScan⟩ := by
    let back := MachineStateEquiv.program (scanStateEquiv A).symm program
    have atScan : back (labels .scan) =
        BinaryNameMachine.scan (tape 0) (tape 2) (labels .scan)
          (some (labels .copyOut)) malformedExit := by
      change MachineStateEquiv.statement (scanStateEquiv A).symm
        (program (labels .scan)) = _
      rw [atLabels .scan]
      exact MachineStateEquiv.statement_symm_statement (scanStateEquiv A) _
    have backForward : MachineStateEquiv.program (scanStateEquiv A) back = program := by
      funext l
      change MachineStateEquiv.statement (scanStateEquiv A)
        (MachineStateEquiv.statement (scanStateEquiv A).symm (program l)) = _
      simpa only [Equiv.symm_symm] using
        MachineStateEquiv.statement_symm_statement (scanStateEquiv A).symm (program l)
    have initialTapes : MaxCutGames.Reduction.MachineTransfer.tapesAt (tape 0) (tape 2)
        base (BinaryNameMachine.frame bits ++ suffix) [] = base := by
      rw [← sourceWord, ← candidateEmpty]
      exact MaxCutGames.Reduction.MachineTransfer.tapesAt_self _ _ _
    have native := BinaryNameMachine.framedTrace (tape 0) (tape 2) (hd 0 2 (by decide))
      (labels .scan) (some (labels .copyOut)) malformedExit back atScan base (ambient, false)
      bits suffix [] none
    simp only [canonical, ↓reduceIte, initialTapes, List.append_nil] at native
    have transported := MachineStateEquiv.trace (scanStateEquiv A) back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, scanStateEquiv, Equiv.coe_fn_mk, BinaryNameMachine.clean,
      clean, afterScan, finalBase, MaxCutGames.Reduction.MachineTransfer.tapesAt] using transported
  have afterScanKey : afterScan (tape 1) = key := by
    simpa [afterScan, finalBase, hd 1 2 (by decide), hd 1 0 (by decide)] using keyWord
  have afterScanCopy : afterScan (tape 3) = [] := by
    simpa [afterScan, finalBase, hd 3 2 (by decide), hd 3 0 (by decide)] using copyEmpty
  have afterScanScratch : afterScan (tape 4) = [] := by
    simpa [afterScan, finalBase, hd 4 2 (by decide), hd 4 0 (by decide)] using scratchEmpty
  have copyRun : (advance (TM2.step program))^[2 * (key.length + 1)]
      (some ⟨some (labels .copyOut), clean ambient, afterScan⟩) =
      some ⟨some (labels .compare), clean ambient, afterCopy⟩ := by
    have h := MachineCopy.copyTrace (tape 1) (tape 3) (tape 4)
      (hd 1 3 (by decide)) (hd 1 4 (by decide)) (hd 3 4 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels .compare)) program
      (atLabels .copyOut) (atLabels .copyBack) afterScan afterScanScratch
      (ambient, false, none) none
    simpa only [afterScanKey, afterScanCopy, List.append_nil, clean, afterCopy] using h
  have candidateWord : afterCopy (tape 2) = bits.reverse := by
    simp [afterCopy, afterScan, hd 2 3 (by decide)]
  have copiedWord : afterCopy (tape 3) = key := by simp [afterCopy]
  have restored : MaxCutGames.Reduction.MachineTransfer.tapesAt (tape 2) (tape 3)
      afterCopy [] [] = finalBase := by
    funext k
    by_cases hc : k = tape 2
    · subst k
      simp [MaxCutGames.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, finalBase,
        hd 2 3 (by decide), hd 2 0 (by decide), candidateEmpty]
    · by_cases hk : k = tape 3
      · subst k
        simp [MaxCutGames.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, finalBase,
          hd 3 0 (by decide), copyEmpty]
      · simp [MaxCutGames.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, hc, hk]
  have comparisonRun : (advance (TM2.step program))^[max bits.length key.length + 1]
      (some ⟨some (labels .compare), clean ambient, afterCopy⟩) =
      some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, finalBase⟩ := by
    let back := MachineStateEquiv.program (compareStateEquiv A).symm program
    have atCompare : back (labels .compare) =
        MachineCompare.loop (tape 2) (tape 3) (labels .compare) equalExit differentExit := by
      change MachineStateEquiv.statement (compareStateEquiv A).symm
        (program (labels .compare)) = _
      rw [atLabels .compare]
      exact MachineStateEquiv.statement_symm_statement (compareStateEquiv A) _
    have backForward : MachineStateEquiv.program (compareStateEquiv A) back = program := by
      funext l
      change MachineStateEquiv.statement (compareStateEquiv A)
        (MachineStateEquiv.statement (compareStateEquiv A).symm (program l)) = _
      simpa only [Equiv.symm_symm] using
        MachineStateEquiv.statement_symm_statement (compareStateEquiv A).symm (program l)
    have native := MachineCompare.compareTrace_fromTapes (tape 2) (tape 3)
      (hd 2 3 (by decide)) (labels .compare) equalExit differentExit back atCompare afterCopy
      ambient none none
    rw [candidateWord, copiedWord, restored, List.length_reverse] at native
    have transported := MachineStateEquiv.trace (compareStateEquiv A) back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, compareStateEquiv, Equiv.coe_fn_mk, clean] using transported
  exact joinTrace_inline_MachineBinaryNameCompare (joinTrace_inline_MachineBinaryNameCompare scanRun copyRun) comparisonRun

/-- Linear runtime in the extracted candidate and stored key lengths. -/
def compareInTime (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (equalExit differentExit malformedExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) =
      instruction tape labels equalExit differentExit malformedExit l)
    (base : K → List Bool) (bits suffix key : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (sourceWord : base (tape 0) = BinaryNameMachine.frame bits ++ suffix)
    (keyWord : base (tape 1) = key)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), clean ambient, base⟩
      (some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, Function.update base (tape 0) suffix⟩)
      (2 * bits.length + 3 * key.length + 4) where
  steps := steps bits.length key.length
  evals_in_steps := compareTrace tape distinct labels equalExit differentExit malformedExit
    program atLabels base bits suffix key canonical sourceWord keyWord
    candidateEmpty copyEmpty scratchEmpty ambient
  steps_le_m := steps_le bits.length key.length

/-- Concrete finite machine; exit labels 0, 1, 2 mean equal, different, malformed. -/
def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label ⊕ Fin 3
  main := .inl .scan
  σ := State Unit
  initialState := clean ()
  m label := match label with
    | .inl l => instruction id Sum.inl (some (.inr 0)) (some (.inr 1)) (some (.inr 2)) l
    | .inr _ => .halt

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end MaxCutGames.BinaryNameCompare

/-!
First-occurrence search over signed, framed binary names. The stream has no
clause markers. Every iteration discards one sign, scans and compares the
actual candidate payload, and increments a Boolean unary counter only after a
mismatch. The preserved key is a reversed payload, never a unary name.

The six explicitly distinct tapes are: stream, preserved key, candidate,
copied key, copy scratch, and unary occurrence counter. Successful search
consumes precisely the prefix through the first matching name, preserves the
unread suffix and all ambient tapes, and returns the three work tapes empty.
The time theorem follows from literal instruction equations and checked
comparison executions, with no supplied loop-body trace premise.
-/

namespace MaxCutGames.BinaryNameSearch

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

abbrev Token := Bool × List Bool

def tokenBits (token : Token) : List Bool :=
  token.1 :: BinaryNameMachine.frame token.2

def stream : List Token → List Bool
  | [] => []
  | token :: tokens => tokenBits token ++ stream tokens

def payloads (tokens : List Token) : List (List Bool) := tokens.map Prod.snd

def afterMatch : List Token → List Bool → List Token
  | [], _ => []
  | token :: tokens, key => if token.2 = key then tokens else afterMatch tokens key

def steps : List Token → List Bool → Nat
  | [], _ => 0
  | token :: tokens, key =>
      1 + BinaryNameCompare.steps token.2.length key.length +
        if token.2 = key then 0 else 1 + steps tokens key

def payloadSize (tokens : List Token) : Nat := (payloads tokens |>.map List.length).sum

@[simp] theorem stream_nil : stream [] = [] := rfl

@[simp] theorem stream_cons (token : Token) (tokens : List Token) :
    stream (token :: tokens) = tokenBits token ++ stream tokens := rfl

@[simp] theorem payloads_nil : payloads [] = [] := rfl

@[simp] theorem payloads_cons (token : Token) (tokens : List Token) :
    payloads (token :: tokens) = token.2 :: payloads tokens := rfl

@[simp] theorem payloadSize_nil : payloadSize [] = 0 := rfl

@[simp] theorem payloadSize_cons (token : Token) (tokens : List Token) :
    payloadSize (token :: tokens) = token.2.length + payloadSize tokens := rfl

@[simp] theorem stream_length (tokens : List Token) :
    (stream tokens).length = 2 * payloadSize tokens + 2 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      simp only [stream_cons, List.length_append, tokenBits, List.length_cons,
        BinaryNameMachine.frame_length, ih, payloadSize_cons]
      omega

/-- Work is linear in the scanned payloads plus one key-copy cost per token. -/
theorem steps_le (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ 2 * payloadSize tokens + (3 * key.length + 6) * tokens.length := by
  induction tokens with
  | nil => simp [steps]
  | cons token tokens ih =>
      have h := BinaryNameCompare.steps_le token.2.length key.length
      simp only [steps, payloadSize_cons, List.length_cons]
      split <;> nlinarith

/-- This bound uses lengths of actual encoded words, not decoded name values. -/
theorem steps_le_stream (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ (3 * key.length + 7) * (stream tokens).length := by
  have h := steps_le tokens key
  rw [stream_length]
  nlinarith

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryNameCompare.State A

abbrev clean (ambient : A) : State A := BinaryNameCompare.clean ambient

inductive Label
  | sign
  | comparison (label : BinaryNameCompare.Label)
  | increment
  deriving DecidableEq, Fintype

def compareTapes (tape : Fin 6 → K) : Fin 5 → K := fun i => tape i.castSucc

omit [DecidableEq K] in
theorem compareTapes_injective (tape : Fin 6 → K) (distinct : Function.Injective tape) :
    Function.Injective (compareTapes tape) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 6 => i.val) (distinct h)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1) (exitAt exit)

def instruction (tape : Fin 6 → K) (labels : Label → Λ)
    (foundExit missingExit malformedExit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .sign =>
      .pop (tape 0) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (finish (some (labels (.comparison .scan)))) (finish missingExit))
  | .comparison l => BinaryNameCompare.instruction (compareTapes tape)
      (fun l => labels (.comparison l)) foundExit (some (labels .increment)) malformedExit l
  | .increment => .push (tape 5) (fun _ => true) (.goto fun _ => labels .sign)

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1.1, base⟩ := by
  cases exit <;> rfl

private theorem update_source_inline_MachineBinaryNameSearch (source counter : K) (distinct : source ≠ counter)
    (base : K → List Bool) (input count replacement : List Bool) :
    Function.update (tapesAt source counter base input count) source replacement =
      tapesAt source counter base replacement count := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hc : k = counter
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hc]

private theorem update_counter_inline_MachineBinaryNameSearch (source counter : K)
    (base : K → List Bool) (input count replacement : List Bool) :
    Function.update (tapesAt source counter base input count) counter replacement =
      tapesAt source counter base input replacement := by
  simp [tapesAt]

private theorem joinTrace_inline_MachineBinaryNameSearch {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

variable (tape : Fin 6 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (foundExit missingExit malformedExit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) =
  instruction tape labels foundExit missingExit malformedExit l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem signStep (sign : Bool) (input counter : List Bool) :
    TM2.step program
      ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (sign :: input) counter⟩ =
      some ⟨some (labels (.comparison .scan)), clean ambient,
        tapesAt (tape 0) (tape 5) base input counter⟩ := by
  have hd : tape 0 ≠ tape 5 := fun h => (by decide : (0 : Fin 6) ≠ 5) (distinct h)
  change some (TM2.stepAux (program (labels .sign)) _ _) = _
  rw [atLabels .sign]
  simp [instruction, TM2.stepAux, clean, BinaryNameCompare.clean, hd, update_source_inline_MachineBinaryNameSearch]

theorem emptyStep (counter : List Bool) :
    TM2.step program
      ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base [] counter⟩ =
      some ⟨missingExit, clean ambient, tapesAt (tape 0) (tape 5) base [] counter⟩ := by
  have hd : tape 0 ≠ tape 5 := fun h => (by decide : (0 : Fin 6) ≠ 5) (distinct h)
  change some (TM2.stepAux (program (labels .sign)) _ _) = _
  rw [atLabels .sign]
  simp [instruction, TM2.stepAux, clean, BinaryNameCompare.clean, hd, update_source_inline_MachineBinaryNameSearch]

omit distinct in
theorem incrementStep (input counter : List Bool) :
    TM2.step program
      ⟨some (labels .increment), clean ambient,
        tapesAt (tape 0) (tape 5) base input counter⟩ =
      some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base input (true :: counter)⟩ := by
  change some (TM2.stepAux (program (labels .increment)) _ _) = _
  rw [atLabels .increment]
  simp [instruction, TM2.stepAux, update_counter_inline_MachineBinaryNameSearch]

/-- One sign is consumed, then the actual shared scan/copy/compare routine runs. -/
theorem tokenTrace (token : Token) (key suffix counter : List Bool)
    (canonical : BinaryNameMachine.canonical token.2 = true)
    (keyWord : base (tape 1) = key.reverse)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[1 + BinaryNameCompare.steps token.2.length key.length]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (tokenBits token ++ suffix) counter⟩) =
      some ⟨if token.2 = key then foundExit else some (labels .increment), clean ambient,
        tapesAt (tape 0) (tape 5) base suffix counter⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let initial := tapesAt (tape 0) (tape 5) base
    (BinaryNameMachine.frame token.2 ++ suffix) counter
  have first : (advance (TM2.step program))^[1]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (tokenBits token ++ suffix) counter⟩) =
      some ⟨some (labels (.comparison .scan)), clean ambient, initial⟩ := by
    simpa only [Function.iterate_one, advance_some, tokenBits, List.cons_append] using
      signStep tape distinct labels foundExit missingExit malformedExit program atLabels
        base ambient token.1 (BinaryNameMachine.frame token.2 ++ suffix) counter
  have second := BinaryNameCompare.compareTrace (compareTapes tape)
    (compareTapes_injective tape distinct) (fun l => labels (.comparison l))
    foundExit (some (labels .increment)) malformedExit program
    (fun l => atLabels (.comparison l)) initial token.2 suffix key.reverse canonical
    (by simp [initial, compareTapes, hd 0 5 (by decide)])
    (by simpa [initial, compareTapes, tapesAt,
      hd 1 0 (by decide), hd 1 5 (by decide)] using keyWord)
    (by simpa [initial, compareTapes, tapesAt, hd 2 0 (by decide), hd 2 5 (by decide)]
      using candidateEmpty)
    (by simpa [initial, compareTapes, tapesAt,
      hd 3 0 (by decide), hd 3 5 (by decide)] using copyEmpty)
    (by simpa [initial, compareTapes, tapesAt,
      hd 4 0 (by decide), hd 4 5 (by decide)] using scratchEmpty)
    ambient
  have heq : token.2.reverse = key.reverse ↔ token.2 = key := by
    constructor
    · intro h
      have := congrArg List.reverse h
      simpa only [List.reverse_reverse] using this
    · intro h; rw [h]
  simp only [List.length_reverse, heq] at second
  rw [show Function.update initial (compareTapes tape 0) suffix =
      tapesAt (tape 0) (tape 5) base suffix counter by
    exact update_source_inline_MachineBinaryNameSearch _ _ (hd 0 5 (by decide)) base _ counter suffix] at second
  exact joinTrace_inline_MachineBinaryNameSearch first second

/-- Successful search returns exactly the first occurrence index. All labels
are literal instruction equations, so this theorem supplies its own body runs. -/
theorem searchTrace (tokens : List Token) (key suffix counter : List Bool)
    (canonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (present : key ∈ payloads tokens)
    (keyWord : base (tape 1) = key.reverse)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[steps tokens key]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) counter⟩) =
      some ⟨foundExit, clean ambient,
        tapesAt (tape 0) (tape 5) base (stream (afterMatch tokens key) ++ suffix)
          (List.replicate ((payloads tokens).idxOf key) true ++ counter)⟩ := by
  induction tokens generalizing counter with
  | nil => simp at present
  | cons token tokens ih =>
      have headCanonical := canonical token (by simp)
      have tailCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true :=
        fun t ht => canonical t (by simp [ht])
      have first := tokenTrace tape distinct labels foundExit missingExit malformedExit
        program atLabels base ambient token key (stream tokens ++ suffix) counter
        headCanonical keyWord candidateEmpty copyEmpty scratchEmpty
      by_cases same : token.2 = key
      · simpa only [steps, same, ite_true, Nat.add_zero, stream_cons,
          List.append_assoc, afterMatch, payloads_cons, List.idxOf_cons_self,
          List.replicate_zero, List.nil_append] using first
      · have remaining : key ∈ payloads tokens := by
          rcases List.mem_cons.mp present with equal | remaining
          · exact False.elim (same equal.symm)
          · exact remaining
        have increment : (advance (TM2.step program))^[1]
            (some ⟨some (labels .increment), clean ambient,
              tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) counter⟩) =
            some ⟨some (labels .sign), clean ambient,
              tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) (true :: counter)⟩ := by
          simpa only [Function.iterate_one, advance_some] using
            incrementStep tape labels foundExit missingExit malformedExit program
              atLabels base ambient (stream tokens ++ suffix) counter
        have rest := ih (true :: counter) tailCanonical remaining
        simp only [same, ite_false] at first
        have full := joinTrace_inline_MachineBinaryNameSearch first (joinTrace_inline_MachineBinaryNameSearch increment rest)
        have counterEq : List.replicate ((payloads tokens).idxOf key) true ++
            (true :: counter) =
            List.replicate ((payloads tokens).idxOf key + 1) true ++ counter := by
          rw [List.replicate_succ']
          simp only [List.append_assoc, List.singleton_append]
        have indexEq : (token.2 :: payloads tokens).idxOf key =
            (payloads tokens).idxOf key + 1 := by
          exact List.idxOf_cons_ne (payloads tokens) same
        simpa only [steps, same, ite_false, stream_cons, List.append_assoc, afterMatch,
          payloads_cons, indexEq, counterEq] using full

/-- Explicit polynomial bound for the actual successful run. -/
def searchInTime (tokens : List Token) (key suffix counter : List Bool)
    (canonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (present : key ∈ payloads tokens)
    (keyWord : base (tape 1) = key.reverse)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) counter⟩
      (some ⟨foundExit, clean ambient,
        tapesAt (tape 0) (tape 5) base (stream (afterMatch tokens key) ++ suffix)
          (List.replicate ((payloads tokens).idxOf key) true ++ counter)⟩)
      ((3 * key.length + 7) * (stream tokens).length) where
  steps := steps tokens key
  evals_in_steps := searchTrace tape distinct labels foundExit missingExit malformedExit
    program atLabels base ambient tokens key suffix counter canonical present keyWord
      candidateEmpty copyEmpty scratchEmpty
  steps_le_m := steps_le_stream tokens key

end Program

/-- Concrete finite-control instantiation; the counter is its designated output. -/
def machine : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 5
  Γ _ := Bool
  Λ := Label ⊕ Fin 3
  main := .inl .sign
  σ := State Unit
  initialState := clean ()
  m label := match label with
    | .inl l => instruction id Sum.inl (some (.inr 0)) (some (.inr 1)) (some (.inr 2)) l
    | .inr _ => .halt

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end MaxCutGames.BinaryNameSearch

namespace MaxCutGames.BinaryLiteralMachine

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

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

/-- Cursor, permanent stream, key, search stream, candidate, key-copy,
copy scratch, index counter, reversed output. -/
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

/-- Polynomial resource bound attached to the proved literal execution. -/
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

end MaxCutGames.BinaryLiteralMachine

end OAI
