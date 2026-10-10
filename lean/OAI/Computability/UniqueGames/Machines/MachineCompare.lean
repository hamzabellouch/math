import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI

section

/-!
# A destructive equality test on two actual Bool stacks

Each loop transition pops both stacks and compares only the two finite head
registers. A sticky mismatch flag makes the loop continue after disagreement.
The final empty/empty test selects an equal or different continuation and resets
all comparison registers. The ambient state and every other tape are preserved.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCompare

open Turing
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := σ × Bool × Option Bool × Option Bool

/-- An optional continuation, without reading or writing any tape. -/
def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- Clear both head registers and the mismatch flag after choosing the exit. -/
def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => (state.1, false, none, none)) (exitAt exit)

/-- The only comparison performed by the program is on two `Option Bool` heads.
In particular, no statement is given a whole-list equality oracle. -/
def loop (left right : K) (loopLabel : Λ) (equalExit differentExit : Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => (state.1, state.2.1, head, state.2.2.2))
    (.pop right (fun state head => (state.1, state.2.1, state.2.2.1, head))
      (.branch (fun state => state.2.2.1.isNone && state.2.2.2.isNone)
        (.branch (fun state => state.2.1) (finish differentExit) (finish equalExit))
        (.load (fun state =>
          (state.1, state.2.1 || decide (state.2.2.1 ≠ state.2.2.2), none, none))
          (.goto fun _ => loopLabel))))

/-- Specification-only outcome, also recording an earlier mismatch. -/
def mismatch (flag : Bool) (leftWord rightWord : List Bool) : Bool :=
  flag || decide (leftWord ≠ rightWord)

@[simp] theorem mismatch_nil_nil (flag : Bool) : mismatch flag [] [] = flag := by
  simp [mismatch]

@[simp] theorem mismatch_nil_cons (flag head : Bool) (tail : List Bool) :
    mismatch flag [] (head :: tail) = true := by simp [mismatch]

@[simp] theorem mismatch_cons_nil (flag head : Bool) (tail : List Bool) :
    mismatch flag (head :: tail) [] = true := by simp [mismatch]

@[simp] theorem mismatch_true (leftWord rightWord : List Bool) :
    mismatch true leftWord rightWord = true := by simp [mismatch]

theorem mismatch_cons (flag leftHead rightHead : Bool) (leftTail rightTail : List Bool) :
    mismatch (flag || decide (leftHead ≠ rightHead)) leftTail rightTail =
      mismatch flag (leftHead :: leftTail) (rightHead :: rightTail) := by
  cases flag <;> cases leftHead <;> cases rightHead <;> simp [mismatch]

@[simp] theorem stepAux_exitAt (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (exitAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) state tapes =
      ⟨exit, (state.1, false, none, none), tapes⟩ := by
  simp [finish, TM2.stepAux]

private theorem update_left (left right : K) (distinct : left ≠ right)
    (base : K → List Bool) (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) left replacement =
      tapesAt left right base replacement rightWord := by
  funext k
  by_cases hl : k = left
  · subst k
    simp [tapesAt, distinct]
  · by_cases hr : k = right
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hl, hr]

private theorem update_right (left right : K) (base : K → List Bool)
    (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) right replacement =
      tapesAt left right base leftWord replacement := by
  simp [tapesAt]

theorem step_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] []⟩ =
      some ⟨if flag then differentExit else equalExit, (ambient, false, none, none),
        tapesAt left right base [] []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] [])) = _
  rw [atLoop]
  cases flag <;>
    simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_nil_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base [] tail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] (head :: tail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_nil (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (head :: tail) []⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base tail []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (head :: tail) [])) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (ambient : σ) (flag : Bool) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail)⟩ =
      some ⟨some loopLabel,
        (ambient, flag || decide (leftHead ≠ rightHead), none, none),
        tapesAt left right base leftTail rightTail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

private theorem trace_left_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] rightWord⟩) =
      some ⟨if mismatch flag [] rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction rightWord generalizing flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, mismatch_nil_nil] using
      step_empty left right distinct loopLabel equalExit differentExit program atLoop base
        ambient flag leftRegister rightRegister
  | cons head tail ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩) = _
    rw [step_nil_cons left right distinct loopLabel equalExit differentExit program atLoop]
    simpa only [mismatch_true, mismatch_nil_cons] using ih true none none

/-- The exact trace with a possibly pre-existing mismatch. Every input symbol
is consumed even when disagreement has already been detected. -/
theorem compareTrace_flag (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if mismatch flag leftWord rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction leftWord generalizing rightWord flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_max] using
      trace_left_empty left right distinct loopLabel equalExit differentExit program atLoop
        base rightWord ambient flag leftRegister rightRegister
  | cons head tail ih =>
    cases rightWord with
    | nil =>
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) []⟩) = _
      rw [step_cons_nil left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [List.length_nil, Nat.max_zero, mismatch_true, mismatch_cons_nil] using
        ih [] true none none
    | cons rightHead rightTail =>
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[max tail.length rightTail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) (rightHead :: rightTail)⟩) = _
      rw [step_cons_cons left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [mismatch_cons] using
        ih rightTail (flag || decide (head ≠ rightHead)) none none

/-- With a clear initial flag, the final continuation tests equality of the
two complete original words. Both tapes and all comparison registers are empty. -/
theorem compareTrace (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if leftWord = rightWord then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  have h := compareTrace_flag left right distinct loopLabel equalExit differentExit program
    atLoop base leftWord rightWord ambient false leftRegister rightRegister
  by_cases heq : leftWord = rightWord <;> simpa [mismatch, heq] using h

theorem compareTrace_fromTapes (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max (base left).length (base right).length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩) =
      some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  simpa only [tapesAt_self] using
    compareTrace left right distinct loopLabel equalExit differentExit program atLoop base
      (base left) (base right) ambient leftRegister rightRegister

/-- The final tape family agrees with the original at every unselected tape. -/
theorem drained_other (left right k : K) (notLeft : k ≠ left) (notRight : k ≠ right)
    (base : K → List Bool) : tapesAt left right base [] [] k = base k :=
  tapesAt_other left right k notLeft notRight base [] []

/-- An actual timed execution witness, with the exact stored transition count. -/
def compareInTime (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩)
      (max (base left).length (base right).length + 1) where
  steps := max (base left).length (base right).length + 1
  evals_in_steps := compareTrace_fromTapes left right distinct loopLabel equalExit differentExit
    program atLoop base ambient leftRegister rightRegister
  steps_le_m := Nat.le_refl _

@[simp] theorem compareInTime_steps (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (compareInTime left right distinct loopLabel equalExit differentExit program atLoop base
      ambient leftRegister rightRegister).steps =
        max (base left).length (base right).length + 1 := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineCompare

end

end OAI
