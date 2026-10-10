import Mathlib.Tactic.DeriveFintype
import OAI.Computability.BinPacking.Arithmetic.BinaryPowerMachine
import OAI.Computability.BinPacking.Computation.MachineExpanderRowDivision
import OAI.Computability.BinPacking.Hardness.LiteralSlotGraph
import OAI.Computability.BinPacking.Search.SearchInitialItemsMachine

namespace OAI

namespace BinPackingGap.FiniteTapeProgram

section

open Turing BinPackingGames.Foundations.Complexity MachineComposition

variable (K S : Type)

structure Data where
  state : S
  tapes : K → List Bool

inductive Action where
  | done
  | push (tape : K) (symbol : S → Bool) (next : Action)
  | pop (tape : K) (save : S → Option Bool → S) (next : Action)
  | peek (tape : K) (save : S → Option Bool → S) (next : Action)
  | load (update : S → S) (next : Action)
  | branch (test : S → Bool) (yes no : Action)

variable {K S}

def Action.statement {Λ : Type} (exit : TM2.Stmt (fun _ : K => Bool) Λ S) :
    Action K S → TM2.Stmt (fun _ : K => Bool) Λ S
  | .done => exit
  | .push k f a => .push k f (a.statement exit)
  | .pop k f a => .pop k f (a.statement exit)
  | .peek k f a => .peek k f (a.statement exit)
  | .load f a => .load f (a.statement exit)
  | .branch f a b => .branch f (a.statement exit) (b.statement exit)

variable [DecidableEq K]

def Action.eval : Action K S → Data K S → Data K S
  | .done, d => d
  | .push k f a, d => a.eval ⟨d.state, Function.update d.tapes k (f d.state :: d.tapes k)⟩
  | .pop k f a, d => a.eval ⟨f d.state (d.tapes k).head?,
      Function.update d.tapes k (d.tapes k).tail⟩
  | .peek k f a, d => a.eval ⟨f d.state (d.tapes k).head?, d.tapes⟩
  | .load f a, d => a.eval ⟨f d.state, d.tapes⟩
  | .branch f a b, d => if f d.state then a.eval d else b.eval d

theorem Action.stepAux_statement {Λ : Type} (a : Action K S)
    (exit : TM2.Stmt (fun _ : K => Bool) Λ S) (d : Data K S) :
    TM2.stepAux (a.statement exit) d.state d.tapes =
      TM2.stepAux exit (a.eval d).state (a.eval d).tapes := by
  induction a generalizing d with
  | done => rfl
  | push k f a ih =>
      simpa only [Action.statement, Action.eval, TM2.stepAux] using
        ih ⟨d.state, Function.update d.tapes k (f d.state :: d.tapes k)⟩
  | pop k f a ih =>
      simpa only [Action.statement, Action.eval, TM2.stepAux] using
        ih ⟨f d.state (d.tapes k).head?, Function.update d.tapes k (d.tapes k).tail⟩
  | peek k f a ih =>
      simpa only [Action.statement, Action.eval, TM2.stepAux] using
        ih ⟨f d.state (d.tapes k).head?, d.tapes⟩
  | load f a ih =>
      simpa only [Action.statement, Action.eval, TM2.stepAux] using ih ⟨f d.state, d.tapes⟩
  | branch f a b iha ihb =>
      cases h : f d.state <;> simp [Action.statement, Action.eval, TM2.stepAux, h, iha, ihb]

inductive Code : Type 1 where
  | atom (action : Action K S)
  | routine (labels : Type) (finite : Fintype labels) (main : labels)
      (program : labels → TM2.Stmt (fun _ : K => Bool) labels S)
  | seq (first second : Code)
  | branch (test : S → Bool) (yes no : Code)
  | loop (guard : Action K S) (test : S → Bool) (body : Code)

@[reducible] def Code.Label : Code (K := K) (S := S) → Type
  | .atom _ => Unit
  | .routine labels _ _ _ => labels
  | .seq a b => a.Label ⊕ b.Label
  | .branch _ a b => Unit ⊕ (a.Label ⊕ b.Label)
  | .loop _ _ a => Unit ⊕ a.Label

instance Code.labelFintype : (c : Code (K := K) (S := S)) → Fintype c.Label
  | .atom _ => inferInstanceAs (Fintype Unit)
  | .routine _ finite _ _ => finite
  | .seq a b =>
      letI := labelFintype a
      letI := labelFintype b
      inferInstanceAs (Fintype (a.Label ⊕ b.Label))
  | .branch _ a b =>
      letI := labelFintype a
      letI := labelFintype b
      inferInstanceAs (Fintype (Unit ⊕ (a.Label ⊕ b.Label)))
  | .loop _ _ a =>
      letI := labelFintype a
      inferInstanceAs (Fintype (Unit ⊕ a.Label))

def Code.entry : (c : Code (K := K) (S := S)) → c.Label
  | .atom _ => ()
  | .routine _ _ main _ => main
  | .seq a _ => .inl a.entry
  | .branch _ _ _ => .inl ()
  | .loop _ _ _ => .inl ()

def jump {Λ : Type} (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ S :=
  match exit with
  | none => .halt
  | some label => .goto (fun _ => label)

@[simp] theorem stepAux_jump {Λ : Type} (exit : Option Λ) (d : Data K S) :
    TM2.stepAux (jump exit) d.state d.tapes = ⟨exit, d.state, d.tapes⟩ := by
  cases exit <;> rfl

def Code.instruction {Λ : Type} : (c : Code (K := K) (S := S)) →
    (c.Label → Λ) → Option Λ → c.Label → TM2.Stmt (fun _ : K => Bool) Λ S
  | .atom a, _, exit, () => a.statement (jump exit)
  | .routine _ _ _ program, labels, exit, l =>
      MachineSubroutine.statement labels exit (program l)
  | .seq a b, labels, _, .inl l =>
      a.instruction (fun l => labels (.inl l)) (some (labels (.inr b.entry))) l
  | .seq _ b, labels, exit, .inr l =>
      b.instruction (fun l => labels (.inr l)) exit l
  | .branch p a b, labels, _, .inl () =>
      .branch p (jump (some (labels (.inr (.inl a.entry)))))
        (jump (some (labels (.inr (.inr b.entry)))))
  | .branch _ a _, labels, exit, .inr (.inl l) =>
      a.instruction (fun l => labels (.inr (.inl l))) exit l
  | .branch _ _ b, labels, exit, .inr (.inr l) =>
      b.instruction (fun l => labels (.inr (.inr l))) exit l
  | .loop g p a, labels, exit, .inl () =>
      g.statement (.branch p (jump (some (labels (.inr a.entry)))) (jump exit))
  | .loop _ _ a, labels, _, .inr l =>
      a.instruction (fun l => labels (.inr l)) (some (labels (.inl ()))) l

inductive Exec : Code (K := K) (S := S) → Data K S → Nat → Data K S → Prop
  | atom (a : Action K S) (d : Data K S) : Exec (.atom a) d 1 (a.eval d)
  | routine {L : Type} (finite : Fintype L) (main : L)
      (program : L → TM2.Stmt (fun _ : K => Bool) L S) (d e : Data K S) (n : Nat) :
      (advance (TM2.step program))^[n]
        (some ⟨some main, d.state, d.tapes⟩) = some ⟨none, e.state, e.tapes⟩ →
      Exec (.routine L finite main program) d n e
  | seq {a b d e f n m} : Exec a d n e → Exec b e m f → Exec (.seq a b) d (n + m) f
  | branch_true {p a b d e n} : p d.state = true → Exec a d n e →
      Exec (.branch p a b) d (n + 1) e
  | branch_false {p a b d e n} : p d.state = false → Exec b d n e →
      Exec (.branch p a b) d (n + 1) e
  | loop_false {g p a d} : p (g.eval d).state = false → Exec (.loop g p a) d 1 (g.eval d)
  | loop_true {g p a d e f n m} : p (g.eval d).state = true →
      Exec a (g.eval d) n e → Exec (.loop g p a) e m f →
      Exec (.loop g p a) d (n + m + 1) f

theorem Exec.trace {c : Code (K := K) (S := S)} {d e : Data K S} {n : Nat}
    (h : Exec c d n e) {Λ : Type} (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ S)
    (labels : c.Label → Λ) (exit : Option Λ)
    (atLabels : ∀ l, program (labels l) = c.instruction labels exit l) :
    (advance (TM2.step program))^[n]
      (some ⟨some (labels c.entry), d.state, d.tapes⟩) =
    some ⟨exit, e.state, e.tapes⟩ := by
  induction h generalizing Λ with
  | atom a d =>
      change some (TM2.stepAux (program (labels ())) d.state d.tapes) = _
      rw [atLabels, Code.instruction, Action.stepAux_statement, stepAux_jump]
  | routine finite main source d e n run =>
      exact MachineSubroutine.trace labels exit source program atLabels n _ _ run
  | @seq a b d e f n m ha hb iha ihb =>
      have first := iha program (fun l => labels (.inl l))
        (some (labels (.inr b.entry))) (fun l => atLabels (.inl l))
      have second := ihb program (fun l => labels (.inr l)) exit
        (fun l => atLabels (.inr l))
      rw [Nat.add_comm n m, Function.iterate_add_apply]
      change (advance (TM2.step program))^[m]
        ((advance (TM2.step program))^[n]
          (some ⟨some (labels (.inl a.entry)), d.state, d.tapes⟩)) = _
      rw [first]
      exact second
  | @branch_true p a b d e n hp h ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step program))^[n]
        (some (TM2.stepAux (program (labels (.inl ()))) d.state d.tapes)) = _
      rw [atLabels]
      simp only [Code.instruction, TM2.stepAux, hp, Bool.cond_true, jump]
      exact ih program (fun l => labels (.inr (.inl l))) exit
        (fun l => atLabels (.inr (.inl l)))
  | @branch_false p a b d e n hp h ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step program))^[n]
        (some (TM2.stepAux (program (labels (.inl ()))) d.state d.tapes)) = _
      rw [atLabels]
      simp only [Code.instruction, TM2.stepAux, hp, Bool.cond_false, jump]
      exact ih program (fun l => labels (.inr (.inr l))) exit
        (fun l => atLabels (.inr (.inr l)))
  | @loop_false g p a d hp =>
      change some (TM2.stepAux (program (labels (.inl ()))) d.state d.tapes) = _
      rw [atLabels, Code.instruction, Action.stepAux_statement]
      simp only [TM2.stepAux, hp, Bool.cond_false, stepAux_jump]
  | @loop_true g p a d e f n m hp hb hl ihb ihl =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step program))^[n + m]
        (some (TM2.stepAux (program (labels (.inl ()))) d.state d.tapes)) = _
      rw [atLabels, Code.instruction, Action.stepAux_statement]
      simp only [TM2.stepAux, hp, Bool.cond_true, jump]
      have body := ihb program (fun l => labels (.inr l))
        (some (labels (.inl ()))) (fun l => atLabels (.inr l))
      rw [Nat.add_comm n m, Function.iterate_add_apply, body]
      exact ihl program labels exit atLabels

def Runs (c : Code (K := K) (S := S)) (d e : Data K S) (budget : Nat) : Prop :=
  ∃ n, Exec c d n e ∧ n ≤ budget

theorem Exec.runs {c : Code (K := K) (S := S)} {d e : Data K S} {n : Nat}
    (run : Exec c d n e) : Runs c d e n := ⟨n, run, le_rfl⟩

theorem Runs.mono {c : Code (K := K) (S := S)} {d e : Data K S} {n m : Nat}
    (run : Runs c d e n) (bound : n ≤ m) : Runs c d e m := by
  rcases run with ⟨t, ht, hbound⟩
  exact ⟨t, ht, hbound.trans bound⟩

theorem Runs.seq {a b : Code (K := K) (S := S)} {d e f : Data K S} {n m : Nat}
    (first : Runs a d e n) (second : Runs b e f m) : Runs (.seq a b) d f (n + m) := by
  rcases first with ⟨i, hi, hin⟩
  rcases second with ⟨j, hj, hjm⟩
  exact ⟨i + j, Exec.seq hi hj, Nat.add_le_add hin hjm⟩

variable [Fintype K] [Fintype S]

def Code.machine (c : Code (K := K) (S := S)) (input output : K) (initial : S) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := c.Label
  main := c.entry
  σ := S
  initialState := initial
  m := c.instruction id none

theorem Code.machine_finiteAlphabet (c : Code (K := K) (S := S))
    (input output : K) (initial : S) :
    MachineFiniteAlphabet.FiniteAlphabet (c.machine input output initial) := by
  intro tape
  change Finite Bool
  infer_instance

def Code.outputsInTime (c : Code (K := K) (S := S)) (input output : K) (initial : S)
    (word result : List Bool) (n budget : Nat)
    (run : Exec c ⟨initial, Function.update (fun _ => []) input word⟩ n
      ⟨initial, Function.update (fun _ => []) output result⟩)
    (bound : n ≤ budget) :
    TM2OutputsInTime (c.machine input output initial) word (some result) budget where
  steps := n
  evals_in_steps := by
    have initialEq : initList (c.machine input output initial) word =
        (⟨some c.entry, initial, Function.update (fun _ => []) input word⟩ :
          (c.machine input output initial).Cfg) := by
      unfold initList
      dsimp only [Code.machine]
      congr 1
      funext k
      by_cases h : k = input
      · subst k; simp [Function.update]; rfl
      · simp [Function.update, h]
    have finalEq : haltList (c.machine input output initial) result =
        (⟨none, initial, Function.update (fun _ => []) output result⟩ :
          (c.machine input output initial).Cfg) := by
      unfold haltList
      dsimp only [Code.machine]
      congr 1
      funext k
      by_cases h : k = output
      · subst k; simp [Function.update]; rfl
      · simp [Function.update, h]
    change (advance (TM2.step (c.instruction id none)))^[n]
      (some (initList (c.machine input output initial) word)) =
        some (haltList (c.machine input output initial) result)
    rw [initialEq, finalEq]
    exact run.trace (c.instruction id none) id none (fun _ => rfl)
  steps_le_m := bound

end

open Turing BinPackingGames.Foundations.Complexity MachineComposition

variable {K S : Type} [DecidableEq K] [Fintype K] [Fintype S]

theorem Exec.stack_length_le {c : Code (K := K) (S := S)}
    {d e : Data K S} {n : Nat} (run : Exec c d n e)
    (input output : K) (initial : S) (k : K) :
    (e.tapes k).length ≤ (d.tapes k).length +
      n * Runtime.programPushBound (c.machine input output initial) := by
  let tm := c.machine input output initial
  have execution : StateTransition.EvalsToInTime tm.step
      (⟨some c.entry, d.state, d.tapes⟩ : tm.Cfg)
      (some ⟨none, e.state, e.tapes⟩) n := {
    steps := n
    evals_in_steps := by
      change (advance (TM2.step (c.instruction id none)))^[n]
        (some ⟨some c.entry, d.state, d.tapes⟩) =
        some ⟨none, e.state, e.tapes⟩
      exact run.trace (c.instruction id none) id none (fun _ => rfl)
    steps_le_m := le_rfl
  }
  exact Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) execution

theorem Runs.stack_length_le {c : Code (K := K) (S := S)}
    {d e : Data K S} {budget : Nat} (run : Runs c d e budget)
    (input output : K) (initial : S) (k : K) :
    (e.tapes k).length ≤ (d.tapes k).length +
      budget * Runtime.programPushBound (c.machine input output initial) := by
  obtain ⟨n, execution, bound⟩ := run
  exact (execution.stack_length_le input output initial k).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ bound) _)

end BinPackingGap.FiniteTapeProgram

namespace BinPackingGap.BooleanTapeCode

open Turing FiniteTapeProgram BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {K A : Type} [DecidableEq K]

abbrev State (A : Type) := (A × Unit) × Option Bool
abbrev Program (K A : Type) := Code (K := K) (S := State A)

def clean (a : A) : State A := ((a, ()), none)

def transfer (source destination : K) : Program K A :=
  .routine Unit inferInstance () (fun _ =>
    MachineTransfer.loopAt source destination id false () none)

theorem transfer_exec (source destination : K) (different : source ≠ destination)
    (base : K → List Bool) (s : State A) :
    Exec (transfer source destination) ⟨s, base⟩ ((base source).length + 1)
      ⟨(s.1, none), MachineTransfer.tapesAt source destination base []
        ((base source).reverse ++ base destination)⟩ := by
  rcases s with ⟨ambient, register⟩
  apply Exec.routine
  have run := MachineTransfer.transferAt_fromTapes source destination different id false () none
    (fun _ : Unit => MachineTransfer.loopAt source destination id false () none)
    rfl base ambient register
  have next_eq : MachineTransfer.nextAt (σ := A × Unit) (Γ := fun _ : K => Bool) destination
      (fun _ : Unit => MachineTransfer.loopAt source destination id false () none) =
      MachineComposition.advance (TM2.step
        (fun _ : Unit => MachineTransfer.loopAt source destination id false () none)) := rfl
  rw [next_eq] at run
  simpa only [List.map_id_fun, id_eq] using run

def copyProgram (source destination scratch : K) :
    Bool → TM2.Stmt (fun _ : K => Bool) Bool (State A)
  | false => MachineTransfer.loopAt source scratch id false false (some true)
  | true => MachineCopy.forkLoop scratch source destination false true none

def copy (source destination scratch : K) : Program K A :=
  .routine Bool inferInstance false (copyProgram source destination scratch)

theorem copy_exec (source destination scratch : K)
    (hSD : source ≠ destination) (hSW : source ≠ scratch) (hDW : destination ≠ scratch)
    (base : K → List Bool) (hW : base scratch = []) (s : State A) :
    Exec (copy source destination scratch) ⟨s, base⟩ (2 * ((base source).length + 1))
      ⟨(s.1, none), Function.update base destination (base source ++ base destination)⟩ := by
  apply Exec.routine
  exact MachineCopy.copyTrace source destination scratch hSD hSW hDW false false true none
    (copyProgram source destination scratch) rfl rfl base hW s.1 s.2

def drain (source : K) : Program K A :=
  .routine Unit inferInstance () (fun _ => MachineDrain.drain source () none)

theorem drain_exec (source : K) (base : K → List Bool) (s : State A) :
    Exec (drain source) ⟨s, base⟩ ((base source).length + 1)
      ⟨(s.1, none), Function.update base source []⟩ := by
  apply Exec.routine
  simpa only [Function.update_eq_self] using
    MachineDrain.drainTrace source () none (fun _ : Unit => MachineDrain.drain source () none)
      rfl base (base source) s.1 s.2

def convert (source destination scratch : K) : Program K A :=
  .routine UnaryToBinaryMachine.Label inferInstance .scan
    (UnaryToBinaryMachine.instruction source destination scratch id none)

theorem convert_exec (source destination scratch : K)
    (hSD : source ≠ destination) (hSW : source ≠ scratch) (hDW : destination ≠ scratch)
    (base : K → List Bool) (a : A) (n initial : Nat) (suffix : List Bool) :
    Exec (convert source destination scratch)
      ⟨clean a, UnaryToBinaryMachine.tapes source destination scratch base
        (encodeWord n ++ suffix) initial.bits []⟩
      (UnaryToBinaryMachine.steps n initial)
      ⟨clean a, UnaryToBinaryMachine.tapes source destination scratch base
        suffix (initial + n).bits []⟩ := by
  apply Exec.routine
  exact UnaryToBinaryMachine.convertTrace source destination scratch hSD hSW hDW id none
    (UnaryToBinaryMachine.instruction source destination scratch id none) (fun _ => rfl)
    base (a, ()) n initial suffix

inductive FrameLabel
  | scan | restore | emit (bit : Bool)
  deriving DecidableEq, Fintype

def frameProgram (source scratch destination : K) :
    FrameLabel → TM2.Stmt (fun _ : K => Bool) FrameLabel (State A)
  | .scan => MachineTransducerCopy.scanLoop source scratch ()
      (fun _ b => .emit b) .restore
  | .emit b => MachineTransducerCopy.emitter destination (fun _ _ => ())
      (fun _ b => [true, b]) .scan () b
  | .restore => MachineTransfer.loopAt scratch source id false .restore none

def framePayload (source scratch destination : K) : Program K A :=
  .routine FrameLabel inferInstance .scan (frameProgram source scratch destination)

theorem framePayload_output (word : List Bool) :
    MachineTransducer.output (fun (_ : Unit) _ => ()) (fun _ b => [true, b]) () word =
      word.flatMap (fun b => [true, b]) := by
  induction word with
  | nil => rfl
  | cons b word ih => simp [MachineTransducer.output, ih]

theorem framePayload_exec (source scratch destination : K)
    (hSW : source ≠ scratch) (hSD : source ≠ destination) (hWD : scratch ≠ destination)
    (base : K → List Bool) (hW : base scratch = []) (a : A) (register : Option Bool) :
    Exec (framePayload source scratch destination) ⟨((a, ()), register), base⟩
      (3 * (base source).length + 2)
      ⟨clean a, Function.update base destination
        (((base source).flatMap (fun b => [true, b])).reverse ++ base destination)⟩ := by
  apply Exec.routine
  simpa only [framePayload_output, clean] using
    MachineTransducerCopy.transduceCopyTrace source scratch destination hSW hSD hWD
      () (fun _ _ => ()) (fun _ b => [true, b]) FrameLabel.scan .restore
      (fun _ b => .emit b) none (frameProgram source scratch destination)
      rfl (fun _ _ => rfl) rfl base hW a () register

def frame (source scratch destination : K) : Program K A :=
  .seq (framePayload source scratch destination)
    (.atom (.push destination (fun _ => false) .done))

theorem frame_eq (word : List Bool) :
    BinPackingCompleteness.BinaryEncoding.frame word = word.flatMap (fun b => [true, b]) ++ [false] := by
  induction word with
  | nil => rfl
  | cons b word ih => simp [BinPackingCompleteness.BinaryEncoding.frame, ih]

theorem frame_exec (source scratch destination : K)
    (hSW : source ≠ scratch) (hSD : source ≠ destination) (hWD : scratch ≠ destination)
    (base : K → List Bool) (hW : base scratch = []) (a : A) (register : Option Bool) :
    Exec (frame source scratch destination) ⟨((a, ()), register), base⟩
      (3 * (base source).length + 3)
      ⟨clean a, Function.update base destination
        ((BinPackingCompleteness.BinaryEncoding.frame (base source)).reverse ++ base destination)⟩ := by
  have first := framePayload_exec source scratch destination hSW hSD hWD base hW a register
  have last := Exec.atom (.push destination (fun _ => false) .done)
    (Data.mk (clean a) (Function.update base destination
      (((base source).flatMap (fun b => [true, b])).reverse ++ base destination)))
  simpa [frame, Action.eval, frame_eq, List.reverse_append, List.append_assoc,
    Nat.add_assoc] using Exec.seq first last

def increment (binary unary scratch : K) : Program K A :=
  .seq (.atom (.push unary (fun _ => false)
    (.push unary (fun _ => true) (.load (fun s => (s.1, none)) .done))))
    (convert unary binary scratch)

theorem increment_exec {n : Nat} (binary unary scratch : K)
    (hUB : unary ≠ binary) (hUW : unary ≠ scratch) (hBW : binary ≠ scratch)
    (base : K → List Bool) (hU : base unary = []) (hW : base scratch = [])
    (hB : base binary = n.bits) (a : A) (register : Option Bool) :
    Exec (increment binary unary scratch) ⟨((a, ()), register), base⟩
      (1 + UnaryToBinaryMachine.steps 1 n)
      ⟨clean a, Function.update base binary (n + 1).bits⟩ := by
  have first := Exec.atom (.push unary (fun _ => false)
    (.push unary (fun _ => true) (.load (fun s => (s.1, none)) .done)))
    (Data.mk ((a, ()), register) base)
  have second := convert_exec unary binary scratch hUB hUW hBW base a 1 n []
  have startEq : UnaryToBinaryMachine.tapes unary binary scratch base
      (encodeWord 1 ++ []) n.bits [] = Function.update base unary [true, false] := by
    funext k
    by_cases hk : k = unary
    · subst k; simp [UnaryToBinaryMachine.tapes, encodeWord, hUB, hUW]
    · by_cases hb : k = binary
      · subst k; simp [UnaryToBinaryMachine.tapes, hBW, hB, hk]
      · by_cases hw : k = scratch
        · subst k; simp [UnaryToBinaryMachine.tapes, hW, hk]
        · simp [UnaryToBinaryMachine.tapes, hk, hb, hw]
  have endEq : UnaryToBinaryMachine.tapes unary binary scratch base [] (n + 1).bits [] =
      Function.update base binary (n + 1).bits := by
    funext k
    by_cases hk : k = unary
    · subst k; simp [UnaryToBinaryMachine.tapes, hUB, hUW, hU]
    · by_cases hb : k = binary
      · subst k; simp [UnaryToBinaryMachine.tapes, hBW]
      · by_cases hw : k = scratch
        · subst k; simp [UnaryToBinaryMachine.tapes, hW, hBW.symm]
        · simp [UnaryToBinaryMachine.tapes, hk, hb, hw]
  rw [startEq, endEq] at second
  exact Exec.seq (by simpa [Action.eval, hU, clean] using first) second

end BinPackingGap.BooleanTapeCode

namespace BinPackingGap.LiteralSlotGraphMachine

open Turing BinPackingGames.Foundations BinPackingGames.Foundations.Target
open FiniteTapeProgram

abbrev NonemptyFormula := {F : Formula // F.clauses ≠ []}

def inputBits (F : NonemptyFormula) : List Bool := Complexity.formulaBits F.val

def graphInput (F : NonemptyFormula) : GraphReductionInput where
  graph := LiteralSlotGraph.graph F.val
  k := 2 * F.val.clauses.length
  k_le := by simp [LiteralSlotGraph.graph, LiteralSlotGraph.vertexCount]; omega
  nonempty := LiteralSlotGraph.graph_edges_nonempty F.val F.property

inductive Tape
  | input | output | accumulator | vertexCount | unary | scratch
  | outerIndex | innerIndex | outerVariable | innerVariable | comparison | innerSource
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .output, .accumulator, .vertexCount,
  .unary, .scratch, .outerIndex, .innerIndex, .outerVariable, .innerVariable, .comparison,
  .innerSource]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

structure Control where
  slot : Fin 3
  remaining : Fin 3
  outerSign : Bool
  innerSign : Bool
  otherHead : Option Bool
  equal : Bool
  deriving DecidableEq, Fintype

def initialControl : Control := ⟨0, 0, false, false, none, true⟩

abbrev State := BooleanTapeCode.State Control
abbrev Program := BooleanTapeCode.Program Tape Control

def initialState : State := BooleanTapeCode.clean initialControl

def saveHead (s : State) (head : Option Bool) : State := (s.1, head)
def mapControl (f : Control → Control) (s : State) : State := ((f s.1.1, ()), s.2)
def resetHead (s : State) : State := (s.1, none)

def skip : Program := .atom .done

def sequence : List Program → Program
  | [] => skip
  | c :: cs => .seq c (sequence cs)

def pushBit (tape : Tape) (bit : Bool) : Program := .atom (.push tape (fun _ => bit) .done)
def changeControl (f : Control → Control) : Program := .atom (.load (mapControl f) .done)

def transfer (source destination : Tape) : Program :=
  BooleanTapeCode.transfer source destination
def copy (source destination scratchTape : Tape) : Program :=
  BooleanTapeCode.copy source destination scratchTape
def drain (source : Tape) : Program := BooleanTapeCode.drain source
def frame (source scratchTape destination : Tape) : Program :=
  BooleanTapeCode.frame source scratchTape destination
def increment (binary : Tape) : Program :=
  BooleanTapeCode.increment binary .unary .scratch

def readVariable (source destination : Tape) : Program :=
  .seq (.loop (.pop source saveHead .done) (fun s => s.2.getD false)
    (.atom (.push destination (fun _ => true) .done)))
    (.atom (.load resetHead .done))

def skipField (source : Tape) : Program :=
  .loop (.pop source saveHead .done) (fun s => s.2.getD false) skip

def readSign (source : Tape) (setSign : Control → Bool → Control) : Program :=
  .atom (.pop source saveHead
    (.load (fun s => ((setSign s.1.1 (s.2.getD false), ()), s.2))
      (.branch (fun s => s.2.getD false)
        (.pop source saveHead (.load resetHead .done))
        (.load resetHead .done))))

def countHeader : Program :=
  .loop (.pop .input saveHead .done) (fun s => s.2.getD false)
    (.atom (.push .unary (fun _ => true) (.push .unary (fun _ => true)
      (.push .vertexCount (fun _ => true) (.push .vertexCount (fun _ => true)
        (.push .vertexCount (fun _ => true) .done))))))

def vertexBody : Program := sequence [
  pushBit .accumulator true,
  frame .outerIndex .scratch .accumulator,
  increment .outerIndex]

def vertices : Program :=
  .loop (.pop .vertexCount saveHead .done) (fun s => s.2.isSome) vertexBody

def compareGuard : Action Tape State :=
  .pop .comparison (fun s h => mapControl (fun a => {a with otherHead := h}) s)
    (.pop .innerVariable saveHead
      (.load (fun s => mapControl
        (fun a => {a with equal := a.equal && decide (a.otherHead = s.2)}) s) .done))

def compareVariables : Program :=
  .seq (changeControl (fun a => {a with equal := true}))
    (.loop compareGuard (fun s => s.1.1.otherHead.isSome || s.2.isSome) skip)

def emitPair : Program := sequence [
  pushBit .accumulator true,
  frame .outerIndex .scratch .accumulator,
  frame .innerIndex .scratch .accumulator]

def isEdge (s : State) : Bool :=
  decide (0 < s.1.1.remaining.val) ||
    (s.1.1.equal && (s.1.1.outerSign != s.1.1.innerSign))

def nextRemaining (a : Control) : Control :=
  {a with remaining := ⟨a.remaining.val - 1, by have := a.remaining.isLt; omega⟩}

def innerBody : Program := sequence [
  readVariable .innerSource .innerVariable,
  readSign .innerSource (fun a b => {a with innerSign := b}),
  copy .outerVariable .comparison .scratch,
  compareVariables,
  .branch isEdge emitPair skip,
  increment .innerIndex,
  changeControl nextRemaining]

def innerLoop : Program :=
  .loop (.peek .innerSource saveHead .done) (fun s => s.2.isSome) innerBody

def startRow (a : Control) : Control :=
  {a with remaining := ⟨2 - a.slot.val, by omega⟩}

def nextSlot (a : Control) : Control :=
  {a with slot := ⟨(a.slot.val + 1) % 3, Nat.mod_lt _ (by decide)⟩}

def outerBody : Program := sequence [
  readVariable .input .outerVariable,
  readSign .input (fun a b => {a with outerSign := b}),
  copy .input .innerSource .scratch,
  copy .outerIndex .innerIndex .scratch,
  increment .innerIndex,
  changeControl startRow,
  innerLoop,
  drain .innerIndex,
  drain .outerVariable,
  increment .outerIndex,
  changeControl nextSlot]

def outerLoop : Program :=
  .loop (.peek .input saveHead .done) (fun s => s.2.isSome) outerBody

def program : Program := sequence [
  skipField .input,
  pushBit .unary false,
  countHeader,
  .atom (.load resetHead .done),
  BooleanTapeCode.convert .unary .outerIndex .scratch,
  frame .outerIndex .scratch .accumulator,
  drain .outerIndex,
  vertices,
  pushBit .accumulator false,
  drain .outerIndex,
  outerLoop,
  pushBit .accumulator false,
  drain .outerIndex,
  transfer .accumulator .output,
  .atom (.load (fun _ => initialState) .done)]

def machine : FinTM2 := program.machine .input .output initialState

theorem machine_finiteAlphabet : Complexity.MachineFiniteAlphabet.FiniteAlphabet machine :=
  program.machine_finiteAlphabet .input .output initialState

end BinPackingGap.LiteralSlotGraphMachine

namespace BinPackingGap.PackingFieldDecodeMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open FiniteTapeProgram

abbrev State (A : Type) := BinaryAddMachine.State A

variable {K A : Type} [DecidableEq K]

def decoderSlots (slots : Fin 3 ↪ K) : Fin 3 ↪ K where
  toFun i := slots ((Equiv.swap (1 : Fin 3) 2) i)
  inj' := fun _ _ h => (Equiv.swap (1 : Fin 3) 2).injective (slots.injective h)

omit [DecidableEq K] in
@[simp] theorem decoderSlots_zero (slots : Fin 3 ↪ K) :
    decoderSlots slots 0 = slots 0 := by
  change slots ((Equiv.swap (1 : Fin 3) 2) 0) = slots 0
  congr 1

omit [DecidableEq K] in
@[simp] theorem decoderSlots_one (slots : Fin 3 ↪ K) :
    decoderSlots slots 1 = slots 2 := by
  change slots ((Equiv.swap (1 : Fin 3) 2) 1) = slots 2
  rw [Equiv.swap_apply_left]

omit [DecidableEq K] in
@[simp] theorem decoderSlots_two (slots : Fin 3 ↪ K) :
    decoderSlots slots 2 = slots 1 := by
  change slots ((Equiv.swap (1 : Fin 3) 2) 2) = slots 1
  rw [Equiv.swap_apply_right]

def code (slots : Fin 3 ↪ K) : Code (K := K) (S := State A) :=
  .routine ExtensionNatMachine.Label inferInstance .scan
    (ExtensionNatMachine.statement (decoderSlots slots) id none none)

def decodedTapes (slots : Fin 3 ↪ K) (base : K → List Bool)
    (payload suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (slots 0) suffix) (slots 2)
    (payload ++ base (slots 2))

theorem decodedTapes_source (slots : Fin 3 ↪ K) (base : K → List Bool)
    (payload suffix : List Bool) : decodedTapes slots base payload suffix (slots 0) = suffix := by
  simp [decodedTapes, slots.injective.ne (show (0 : Fin 3) ≠ 2 by decide)]

theorem decodedTapes_scratch (slots : Fin 3 ↪ K) (base : K → List Bool)
    (payload suffix : List Bool) : decodedTapes slots base payload suffix (slots 1) = base (slots 1) := by
  simp [decodedTapes, slots.injective.ne (show (1 : Fin 3) ≠ 0 by decide),
    slots.injective.ne (show (1 : Fin 3) ≠ 2 by decide)]

theorem decodedTapes_destination (slots : Fin 3 ↪ K) (base : K → List Bool)
    (payload suffix : List Bool) :
    decodedTapes slots base payload suffix (slots 2) = payload ++ base (slots 2) := by
  simp [decodedTapes]

theorem decodedTapes_other (slots : Fin 3 ↪ K) (base : K → List Bool)
    (payload suffix : List Bool) (k : K) (hs : k ≠ slots 0) (hd : k ≠ slots 2) :
    decodedTapes slots base payload suffix k = base k := by simp [decodedTapes, hs, hd]

theorem decodeNat_exec (slots : Fin 3 ↪ K) (base : K → List Bool)
    (ambient : A) (n : Nat) (suffix : List Bool)
    (sourceWord : base (slots 0) = BinaryEncoding.natBits n ++ suffix)
    (scratchEmpty : base (slots 1) = []) :
    Exec (code slots) ⟨BinaryAddMachine.clean ambient, base⟩ (2 * n.size + 2)
      ⟨BinaryAddMachine.clean ambient, decodedTapes slots base n.bits suffix⟩ := by
  apply Exec.routine
  have run := ExtensionNatMachine.natTrace (decoderSlots slots) id none none
    (ExtensionNatMachine.statement (decoderSlots slots) id none none) (fun _ => rfl)
    base n suffix (by simpa using sourceWord) (by simpa using scratchEmpty) ambient
  simpa only [ExtensionNatMachine.resultTapes, decodedTapes, decoderSlots_zero,
    decoderSlots_one, id_eq] using run

theorem decodeNat_steps (n : Nat) :
    2 * n.size + 2 = (BinaryEncoding.natBits n).length + 1 := by
  simp [Nat.add_assoc]

def decodeNatInTime {Λ : Type} (slots : Fin 3 ↪ K)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A))
    (labels : (code (A := A) slots).Label → Λ) (exit : Option Λ)
    (atLabels : ∀ l, program (labels l) = (code slots).instruction labels exit l)
    (base : K → List Bool) (ambient : A) (n : Nat) (suffix : List Bool)
    (sourceWord : base (slots 0) = BinaryEncoding.natBits n ++ suffix)
    (scratchEmpty : base (slots 1) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (code slots).entry), BinaryAddMachine.clean ambient, base⟩
      (some ⟨exit, BinaryAddMachine.clean ambient, decodedTapes slots base n.bits suffix⟩)
      ((BinaryEncoding.natBits n).length + 1) where
  steps := 2 * n.size + 2
  evals_in_steps := by
    change (advance (TM2.step program))^[2 * n.size + 2]
      (some ⟨some (labels (code slots).entry), BinaryAddMachine.clean ambient, base⟩) =
      some ⟨exit, BinaryAddMachine.clean ambient, decodedTapes slots base n.bits suffix⟩
    exact (decodeNat_exec slots base ambient n suffix sourceWord scratchEmpty).trace
      program labels exit atLabels
  steps_le_m := (decodeNat_steps n).le

def machine : FinTM2 :=
  (code (A := Unit) (Function.Embedding.refl (Fin 3))).machine 0 2 (BinaryAddMachine.clean ())

theorem machine_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet machine :=
  (code (A := Unit) (Function.Embedding.refl (Fin 3))).machine_finiteAlphabet 0 2
    (BinaryAddMachine.clean ())

end BinPackingGap.PackingFieldDecodeMachine

namespace BinPackingGap.PackingPowerProgram

open Turing
open BinPackingGames.Foundations.Complexity
open FiniteTapeProgram

variable {K A : Type} [DecidableEq K]

structure Ready (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat) : Prop where
  baseWord : base (slots 0) = a.bits
  outputEmpty : base (slots 1) = []
  tallyWord : base (slots 9) = List.replicate n true
  workspace : BinaryPowerMachine.Workspace slots base

def resultTapes (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat) : K → List Bool :=
  Function.update (Function.update base (slots 9) []) (slots 1) (a ^ n).bits

@[simp] theorem resultTapes_output (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat) :
    resultTapes slots base a n (slots 1) = (a ^ n).bits := by
  simp [resultTapes]

@[simp] theorem resultTapes_tally (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat) :
    resultTapes slots base a n (slots 9) = [] := by
  have h : slots 9 ≠ slots 1 := slots.injective.ne (by decide)
  simp [resultTapes, h]

theorem resultTapes_other (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat)
    (k : K) (output : k ≠ slots 1) (tally : k ≠ slots 9) :
    resultTapes slots base a n k = base k := by
  simp [resultTapes, output, tally]

@[simp] theorem resultTapes_base (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat) :
    resultTapes slots base a n (slots 0) = base (slots 0) :=
  resultTapes_other slots base a n (slots 0)
    (slots.injective.ne (by decide)) (slots.injective.ne (by decide))

theorem resultTapes_workspace (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat)
    (workspace : BinaryPowerMachine.Workspace slots base) :
    BinaryPowerMachine.Workspace slots (resultTapes slots base a n) := by
  intro i hi hi9
  have hi1 : i ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    omega
  have hi9' : i ≠ 9 := by
    intro h
    exact hi9 (congrArg Fin.val h)
  rw [resultTapes_other slots base a n (slots i)
    (slots.injective.ne hi1) (slots.injective.ne hi9')]
  exact workspace i hi hi9

noncomputable def budget (a n : Nat) : Nat :=
  BinaryPowerMachine.timePolynomial.eval (a.size + n)

def code (slots : Fin 11 ↪ K) : Code (K := K) (S := BinaryAddMachine.State A) :=
  .routine BinaryPowerMachine.Label inferInstance .initialize (BinaryPowerMachine.program slots)

noncomputable def runInTime (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat)
    (ready : Ready slots base a n) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (BinaryPowerMachine.program (A := A) slots))
      ⟨some .initialize, BinaryAddMachine.clean ambient, base⟩
      (some ⟨none, BinaryAddMachine.clean ambient, resultTapes slots base a n⟩)
      (budget a n) := by
  have run := BinaryPowerMachine.powerInPolynomialTime slots id none
    (BinaryPowerMachine.program (A := A) slots) (fun _ => rfl)
    base a (List.replicate n true) ready.baseWord ready.outputEmpty ready.tallyWord
    ready.workspace ambient
  simpa only [id_eq, List.length_replicate, resultTapes, budget] using run

theorem exec (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat)
    (ready : Ready slots base a n) (ambient : A) :
    ∃ steps ≤ budget a n,
      Exec (code (A := A) slots) ⟨BinaryAddMachine.clean ambient, base⟩ steps
        ⟨BinaryAddMachine.clean ambient, resultTapes slots base a n⟩ := by
  let run := runInTime slots base a n ready ambient
  refine ⟨run.steps, run.steps_le_m, ?_⟩
  refine Exec.routine inferInstance (BinaryPowerMachine.Label.initialize)
    (BinaryPowerMachine.program slots)
    ⟨BinaryAddMachine.clean ambient, base⟩
    ⟨BinaryAddMachine.clean ambient, resultTapes slots base a n⟩ run.steps ?_
  have trace := run.evals_in_steps
  change (MachineComposition.advance (TM2.step (BinaryPowerMachine.program (A := A) slots)))^[run.steps]
    (some (⟨some BinaryPowerMachine.Label.initialize, BinaryAddMachine.clean ambient, base⟩ :
      TM2.Cfg (fun _ : K => Bool) BinaryPowerMachine.Label (BinaryAddMachine.State A))) =
    some ⟨none, BinaryAddMachine.clean ambient, resultTapes slots base a n⟩ at trace
  exact trace

end BinPackingGap.PackingPowerProgram

end OAI
