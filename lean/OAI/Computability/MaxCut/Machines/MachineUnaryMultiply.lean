import Mathlib
import OAI.Computability.MaxCut.Machines.MachineSequential
import OAI.Computability.MaxCut.Machines.MachineSubroutine

namespace OAI

/-!
An actual five-stack unary multiplication subroutine. Both isolated input
fields are preserved. The product field prefixes the previous output stack;
the counter and scratch return empty and all other stacks are framed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

inductive Label
  | copyDrain | copyFork | seed | guard | scan | emitFalse | emitTrue | restore | finish
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyDrain, .copyFork, .seed, .guard, .scan,
  .emitFalse, .emitTrue, .restore, .finish]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := (σ × Unit) × Option Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (_ : Unit) (bit : Bool) : List Bool := if bit then [true] else []

def emitterLabel {Λ : Type} (labels : Label → Λ) (_ : Unit) (bit : Bool) : Λ :=
  if bit then labels .emitTrue else labels .emitFalse

variable {K Λ σ : Type} [DecidableEq K]

/-- Slots 0 and 1 contain the operands, 2 the output, 3 the counter, and
4 the reusable empty scratch. The code is independent of operand values. -/
def statement (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .copyDrain => Reduction.MachineTransfer.loopAt (slots 1) (slots 4) id false
      (labels .copyDrain) (some (labels .copyFork))
  | .copyFork => MachineCopy.forkLoop (slots 4) (slots 1) (slots 3) false
      (labels .copyFork) (some (labels .seed))
  | .seed => .push (slots 2) (fun _ => false) (.goto fun _ => labels .guard)
  | .guard => MachineUnaryCounter.guard (slots 3) (labels .scan) (labels .finish)
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore)
  | .emitFalse => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () false
  | .emitTrue => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () true
  | .restore => Reduction.MachineTransfer.loopAt (slots 4) (slots 0) id false
      (labels .restore) (some (labels .guard))
  | .finish => .pop (slots 3) (fun state _ => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots 2) exit)

def program (slots : Fin 5 ↪ K) : Label → TM2.Stmt (Alphabet (K := K)) Label (State σ) :=
  statement slots id none

def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .copyDrain
  σ := State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl (Fin 5))

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (product : ℕ) : K → List Bool :=
  Function.update base (slots 2) (encodeWord product ++ base (slots 2))

@[simp] theorem resultTapes_output (slots : Fin 5 ↪ K) (base : K → List Bool) (p : ℕ) :
    resultTapes slots base p (slots 2) = encodeWord p ++ base (slots 2) := by
  simp [resultTapes]

theorem resultTapes_other (slots : Fin 5 ↪ K) (base : K → List Bool) (p : ℕ)
    (k : K) (hk : k ≠ slots 2) : resultTapes slots base p k = base k := by
  simp [resultTapes, hk]

def bodySteps (a : ℕ) : ℕ := 3 * (a + 1) + 2
def steps (a b : ℕ) : ℕ := 3 * a * b + 8 * b + 7

private theorem output_encodeWord_inline_MachineUnaryMultiply (a : ℕ) :
    Reduction.MachineTransducer.output transition payload () (encodeWord a) =
      List.replicate a true := by
  induction a with
  | zero => simp [encodeWord, Reduction.MachineTransducer.output, payload]
  | succ a ih =>
    simpa only [encodeWord, List.replicate_succ, List.cons_append,
      Reduction.MachineTransducer.output, payload, Bool.cond_true, transition,
      ite_true, List.singleton_append, List.nil_append] using congrArg (List.cons true) ih

private theorem prepend_payload_inline_MachineUnaryMultiply (a p : ℕ) (suffix : List Bool) :
    List.replicate a true ++ (encodeWord p ++ suffix) = encodeWord (a + p) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

/-- The accumulator is indexed by the remaining number of outer iterations. -/
def loopBase (slots : Fin 5 ↪ K) (base : K → List Bool) (a b r : ℕ) : K → List Bool :=
  resultTapes slots base (a * (b - r))

private theorem bodyTrace_inline_MachineUnaryMultiply (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b r : ℕ) (hr : r < b)
    (operand : base (slots 0) = encodeWord a) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[bodySteps a]
      (some (MachineCountedLoop.bodyConfiguration (slots 3) (labels .scan) []
        (fun _ => (ambient, ())) (loopBase slots base a b) r)) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) r) := by
  have h04 : slots 0 ≠ slots 4 := slots.injective.ne (by decide)
  have h02 : slots 0 ≠ slots 2 := slots.injective.ne (by decide)
  have h42 : slots 4 ≠ slots 2 := slots.injective.ne (by decide)
  have h03 : slots 0 ≠ slots 3 := slots.injective.ne (by decide)
  have h43 : slots 4 ≠ slots 3 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let start := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b (r + 1)) r []
  have hstartA : start (slots 0) = encodeWord a := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h03, h02, operand]
  have hstartScratch : start (slots 4) = [] := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h43, h42, scratchEmpty]
  have hscan : p (labels .scan) = MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore) := atLabels .scan
  have hemit : ∀ control bit, p (emitterLabel labels control bit) =
      MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) control bit := by
    intro control bit
    cases control
    cases bit <;> exact atLabels _
  have hrestore : p (labels .restore) = Reduction.MachineTransfer.loopAt (slots 4) (slots 0)
      id false (labels .restore) (some (labels .guard)) := atLabels .restore
  have hcopy := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 4) (slots 2)
    h04 h02 h42 () transition payload (labels .scan) (labels .restore) (emitterLabel labels)
    (some (labels .guard)) p hscan hemit hrestore start hstartScratch ambient () none
  rw [hstartA, output_encodeWord_inline_MachineUnaryMultiply, List.reverse_replicate] at hcopy
  have hcount : a + a * (b - (r + 1)) = a * (b - r) := by
    have hr' : b - r = b - (r + 1) + 1 := by omega
    rw [hr']
    ring
  have hfinish : Function.update start (slots 2)
      (List.replicate a true ++ start (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b r) r [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp only [Function.update_self]
      simp only [start, MachineUnaryCounter.counterTapes_other (slots 3) (slots 2) h23,
        loopBase, resultTapes_output]
      rw [prepend_payload_inline_MachineUnaryMultiply, hcount]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [start, MachineUnaryCounter.counterTapes, hk2]
      · simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  rw [hfinish] at hcopy
  simpa only [bodySteps, encodeWord, List.length_append, List.length_replicate,
    List.length_singleton, MachineCountedLoop.bodyConfiguration,
    MachineCountedLoop.guardConfiguration] using hcopy

private theorem totalSteps_eq_inline_MachineUnaryMultiply (a b : ℕ) :
    MachineCountedLoop.totalSteps (fun _ => bodySteps a) b = b * (bodySteps a + 1) + 1 := by
  simp [MachineCountedLoop.totalSteps, Nat.mul_add, Nat.add_assoc]

/-- Exact execution in any ambient program containing the nine declared
statements. The body traces are derived from the actual copy transducer. -/
theorem multiplyTrace (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps a b]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
  have h13 : slots 1 ≠ slots 3 := slots.injective.ne (by decide)
  have h14 : slots 1 ≠ slots 4 := slots.injective.ne (by decide)
  have h34 : slots 3 ≠ slots 4 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let copied := Function.update base (slots 3) (encodeWord b)
  have hcopy : (MachineComposition.advance (TM2.step p))^[2 * (b + 2)]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .seed), ((ambient, ()), none), copied⟩ := by
    have h := MachineCopy.copyTrace (slots 1) (slots 3) (slots 4) h13 h14 h34 false
      (labels .copyDrain) (labels .copyFork) (some (labels .seed)) p
      (atLabels .copyDrain) (atLabels .copyFork) base scratchEmpty (ambient, ()) register
    simpa only [copied, operandB, counterEmpty, List.append_nil, encodeWord, List.length_append,
      List.length_replicate, List.length_singleton, Nat.add_assoc, Nat.reduceAdd] using h
  have hseedTapes : Function.update copied (slots 2) (false :: copied (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b b) b [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h23, encodeWord]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [copied, MachineUnaryCounter.counterTapes, hk2]
      · simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), ((ambient, ()), none), copied⟩) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) b) := by
    change some (TM2.stepAux (p (labels .seed)) ((ambient, ()), none) copied) = _
    rw [atLabels .seed]
    change some (⟨some (labels .guard), ((ambient, ()), none),
      Function.update copied (slots 2) (false :: copied (slots 2))⟩ :
        TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
    rw [hseedTapes]
    rfl
  have hloop := MachineCountedLoop.loopTrace (slots 3) (labels .guard) (labels .scan)
    (labels .finish) p (atLabels .guard) [] (fun _ => (ambient, ())) (fun _ => none)
    (loopBase slots base a b) (fun _ => bodySteps a) b
    (fun r hr => bodyTrace_inline_MachineUnaryMultiply slots labels exit p atLabels base a b r hr operandA scratchEmpty ambient)
  let finalCounter := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b 0) 0 []
  have hfinishTapes : Function.update finalCounter (slots 3) ((finalCounter (slots 3)).tail) =
      resultTapes slots base (a * b) := by
    funext k
    by_cases hk3 : k = slots 3
    · subst k
      simp [finalCounter, MachineUnaryCounter.counterTapes, encodeWord, resultTapes,
        Ne.symm h23, counterEmpty]
    · simp [finalCounter, MachineUnaryCounter.counterTapes, loopBase, hk3]
  have hfinish : (MachineComposition.advance (TM2.step p))^[1]
      (some (MachineCountedLoop.exitConfiguration (slots 3) (labels .finish) []
        (fun _ => (ambient, ())) (loopBase slots base a b))) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
    change some (TM2.stepAux (p (labels .finish)) ((ambient, ()), none) finalCounter) = _
    rw [atLabels .finish]
    cases exit <;>
      simpa only [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt] using
        congrArg (fun tapes => some (⟨_, ((ambient, ()), none), tapes⟩ :
          TM2.Cfg (Alphabet (K := K)) Λ (State σ))) hfinishTapes
  rw [show steps a b = 1 + (MachineCountedLoop.totalSteps (fun _ => bodySteps a) b +
      (1 + 2 * (b + 2))) by rw [totalSteps_eq_inline_MachineUnaryMultiply]; unfold steps bodySteps; ring]
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    hcopy, hseed, hloop]
  exact hfinish

/-- A time witness with the exact transition count, including restoration
of the operand delimiter and removal of the counter delimiter. -/
def multiplyInTime (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩) (steps a b) where
  steps := steps a b
  evals_in_steps := multiplyTrace slots labels exit p atLabels base a b operandA operandB
    counterEmpty scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

noncomputable def timePolynomial : Polynomial ℕ :=
  Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 8 * Polynomial.X + Polynomial.C 7

theorem steps_le_timePolynomial (a b : ℕ) :
    steps a b ≤ timePolynomial.eval (a + b + 2) := by
  have ha : a ≤ a + b + 2 := by omega
  have hb : b ≤ a + b + 2 := by omega
  have hab := Nat.mul_le_mul ha hb
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  unfold steps
  nlinarith

/-- Both input stacks, both restored work stacks, and every unrelated stack
are preserved because only the output stack differs at the actual endpoint. -/
theorem multiplyFrame (slots : Fin 5 ↪ K) (base : K → List Bool) (a b : ℕ)
    (k : K) (hk : k ≠ slots 2) :
    resultTapes slots base (a * b) k = base k := resultTapes_other slots base _ k hk

/-- The fixed finite program realizes the trace without any caller-code
or abstract-computability hypothesis. -/
theorem programTrace (slots : Fin 5 ↪ K) (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program (σ := σ) slots)))^[steps a b]
      (some ⟨some .copyDrain, ((ambient, ()), register), base⟩) =
      some ⟨none, ((ambient, ()), none), resultTapes slots base (a * b)⟩ :=
  multiplyTrace slots id none (program slots) (fun _ => rfl) base a b
    operandA operandB counterEmpty scratchEmpty ambient register

/-- The fixed program's genuine execution fits a quadratic polynomial in
the combined lengths of its two encoded operand fields. -/
def programInPolynomialTime (slots : Fin 5 ↪ K) (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ) slots))
      ⟨some .copyDrain, ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), resultTapes slots base (a * b)⟩)
      (timePolynomial.eval ((encodeWord a).length + (encodeWord b).length)) where
  steps := steps a b
  evals_in_steps := programTrace slots base a b operandA operandB counterEmpty scratchEmpty ambient register
  steps_le_m := by
    have hlength : (encodeWord a).length + (encodeWord b).length = a + b + 2 := by
      simp only [encodeWord, List.length_append, List.length_replicate, List.length_singleton]
      omega
    rw [hlength]
    exact steps_le_timePolynomial a b

end MaxCutGames.Foundations.Complexity.MachineUnaryMultiply

namespace MaxCutGames.Foundations.Complexity.MachineUnaryAddAt

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (destination : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun state => (state.1, none)) (exitAt destination exit)

/-- A fixed finite statement; arithmetic is performed by the physical unary tapes. -/
def loop (source destination : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push destination (fun _ => true) (.goto fun _ => loopLabel))
      (.branch (fun state => state.2.isSome)
        (.push source (fun _ => false) (finish destination exit))
        (finish destination exit)))

omit [DecidableEq K] in
theorem loopPushBound (source destination : K) (loopLabel : Λ) (exit : Option Λ) :
    Runtime.statementPushBound (loop (σ := σ) source destination loopLabel exit) = 1 := by
  cases exit <;> rfl

/-- A caller's tape frame with the two unary prefixes and their unread suffixes. -/
def unaryTapes (source destination : K) (base : K → List Bool) (a b : Nat)
    (sourceSuffix destinationSuffix : List Bool) : K → List Bool :=
  tapesAt source destination base (encodeWord a ++ sourceSuffix)
    (encodeWord b ++ destinationSuffix)

@[simp] theorem unaryTapes_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool) :
    unaryTapes source destination base a b sourceSuffix destinationSuffix source =
      encodeWord a ++ sourceSuffix := by
  simp [unaryTapes, distinct]

@[simp] theorem unaryTapes_destination (source destination : K)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool) :
    unaryTapes source destination base a b sourceSuffix destinationSuffix destination =
      encodeWord b ++ destinationSuffix := by
  simp [unaryTapes]

theorem unaryTapes_other (source destination other : K)
    (notSource : other ≠ source) (notDestination : other ≠ destination)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool) :
    unaryTapes source destination base a b sourceSuffix destinationSuffix other =
      base other := by
  simp [unaryTapes, tapesAt, notSource, notDestination]

private theorem update_source_inline_MachineUnaryAddAt (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

private theorem update_destination_inline_MachineUnaryAddAt (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  funext k
  by_cases hd : k = destination
  · subst k
    simp [tapesAt]
  · simp [tapesAt, hd]

theorem stepAux_true (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool)
    (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (tapesAt source destination base (true :: input) output) =
      ⟨some loopLabel, (ambient, some true),
        tapesAt source destination base input (true :: output)⟩ := by
  simp [loop, TM2.stepAux, distinct, update_source_inline_MachineUnaryAddAt, update_destination_inline_MachineUnaryAddAt]

/-- The zero branch restores the delimiter, clears the register, and exits. -/
theorem stepAux_false (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool)
    (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (tapesAt source destination base (false :: input) output) =
      ⟨exit, (ambient, none), tapesAt source destination base (false :: input) output⟩ := by
  cases exit <;> simp [loop, finish, exitAt, TM2.stepAux, distinct, update_source_inline_MachineUnaryAddAt]

theorem stepAux_succ (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool) (a b : Nat)
    (sourceSuffix destinationSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix) =
      ⟨some loopLabel, (ambient, some true),
        unaryTapes source destination base a (b + 1) sourceSuffix destinationSuffix⟩ := by
  simpa only [unaryTapes, encodeWord, List.replicate_succ, List.cons_append] using
    stepAux_true source destination distinct loopLabel exit base
      (encodeWord a ++ sourceSuffix) (encodeWord b ++ destinationSuffix) ambient register

theorem stepAux_zero (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool) (b : Nat)
    (sourceSuffix destinationSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (unaryTapes source destination base 0 b sourceSuffix destinationSuffix) =
      ⟨exit, (ambient, none),
        unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ := by
  simpa only [unaryTapes, encodeWord, List.replicate_zero, List.nil_append,
    List.singleton_append] using
    stepAux_false source destination distinct loopLabel exit base sourceSuffix
      (encodeWord b ++ destinationSuffix) ambient register

theorem step_succ (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some loopLabel, (ambient, register),
      unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix⟩ =
      some ⟨some loopLabel, (ambient, some true),
        unaryTapes source destination base a (b + 1) sourceSuffix destinationSuffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix)) = _
  rw [atLoop, stepAux_succ source destination distinct]

theorem step_zero (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some loopLabel, (ambient, register),
      unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (unaryTapes source destination base 0 b sourceSuffix destinationSuffix)) = _
  rw [atLoop, stepAux_zero source destination distinct]

/-- Exactly `a` positive-bit transitions followed by the delimiter transition. -/
theorem addTrace (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[a + 1]
      (some ⟨some loopLabel, (ambient, register),
        unaryTapes source destination base a b sourceSuffix destinationSuffix⟩) =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 (a + b) sourceSuffix destinationSuffix⟩ := by
  induction a generalizing b register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
      step_zero source destination distinct loopLabel exit program atLoop
        base b sourceSuffix destinationSuffix ambient register
  | succ a ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[a + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix⟩) = _
    rw [step_succ source destination distinct loopLabel exit program atLoop]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (b + 1) (some true)

/-- The same actual execution from a caller's supplied tape configuration. -/
theorem addFromTapes (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (sourceInput : base source = encodeWord a ++ sourceSuffix)
    (destinationInput : base destination = encodeWord b ++ destinationSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[a + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 (a + b) sourceSuffix destinationSuffix⟩ := by
  have hbase : unaryTapes source destination base a b sourceSuffix destinationSuffix =
      base := by
    simp only [unaryTapes, ← sourceInput, ← destinationInput, tapesAt_self]
  have h := addTrace source destination distinct loopLabel exit program atLoop
    base a b sourceSuffix destinationSuffix ambient register
  rw [hbase] at h
  exact h

/-- A composable time witness whose stored transition count is exactly `a + 1`. -/
def addInTime (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (sourceInput : base source = encodeWord a ++ sourceSuffix)
    (destinationInput : base destination = encodeWord b ++ destinationSuffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 (a + b) sourceSuffix destinationSuffix⟩)
      (a + 1) where
  steps := a + 1
  evals_in_steps := addFromTapes source destination distinct loopLabel exit program atLoop
    base a b sourceSuffix destinationSuffix sourceInput destinationInput ambient register
  steps_le_m := Nat.le_refl _

@[simp] theorem addInTime_steps (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (sourceInput : base source = encodeWord a ++ sourceSuffix)
    (destinationInput : base destination = encodeWord b ++ destinationSuffix)
    (ambient : σ) (register : Option Bool) :
    (addInTime source destination distinct loopLabel exit program atLoop base a b
      sourceSuffix destinationSuffix sourceInput destinationInput ambient register).steps =
      a + 1 := rfl

end MaxCutGames.Foundations.Complexity.MachineUnaryAddAt

/-!
One actual Horner step on unary field stacks. Multiplication and addition are
executions of the same finite program. All three operands are preserved; only
the output stack receives a new field and both work stacks return empty.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRadixStep

open Turing

inductive Label
  | multiply (label : MachineUnaryMultiply.Label)
  | digitDrain | digitFork | add | finish
  deriving DecidableEq, Fintype

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := MachineUnaryMultiply.State σ

variable {K Λ σ : Type}

/-- Multiplication uses radix, accumulator, output, counter, and scratch,
skipping the independently preserved digit stack. -/
def multiplySlots (slots : Fin 6 ↪ K) : Fin 5 ↪ K :=
  (Fin.succAboveEmb (2 : Fin 6)).trans slots

@[simp] theorem multiplySlots_zero (slots : Fin 6 ↪ K) : multiplySlots slots 0 = slots 0 := rfl
@[simp] theorem multiplySlots_one (slots : Fin 6 ↪ K) : multiplySlots slots 1 = slots 1 := rfl
@[simp] theorem multiplySlots_two (slots : Fin 6 ↪ K) : multiplySlots slots 2 = slots 3 := rfl
@[simp] theorem multiplySlots_three (slots : Fin 6 ↪ K) : multiplySlots slots 3 = slots 4 := rfl
@[simp] theorem multiplySlots_four (slots : Fin 6 ↪ K) : multiplySlots slots 4 = slots 5 := rfl

variable [DecidableEq K]

def statement (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .multiply label => MachineUnaryMultiply.statement (multiplySlots slots)
      (fun l => labels (.multiply l)) (some (labels .digitDrain)) label
  | .digitDrain => Reduction.MachineTransfer.loopAt (slots 2) (slots 5) id false
      (labels .digitDrain) (some (labels .digitFork))
  | .digitFork => MachineCopy.forkLoop (slots 5) (slots 2) (slots 4) false
      (labels .digitFork) (some (labels .add))
  | .add => MachineUnaryAddAt.loop (slots 4) (slots 3) (labels .add) (some (labels .finish))
  | .finish => .pop (slots 4) (fun state _ => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots 3) exit)

def program (slots : Fin 6 ↪ K) : Label → TM2.Stmt (Alphabet (K := K)) Label (State σ) :=
  statement slots id none

def machine : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Label
  main := .multiply .copyDrain
  σ := State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl (Fin 6))

def resultTapes (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) : K → List Bool :=
  Function.update base (slots 3) (encodeWord value ++ base (slots 3))

@[simp] theorem resultTapes_output (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) :
    resultTapes slots base value (slots 3) = encodeWord value ++ base (slots 3) := by
  simp [resultTapes]

theorem resultTapes_other (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ)
    (k : K) (hk : k ≠ slots 3) : resultTapes slots base value k = base k := by
  simp [resultTapes, hk]

def steps (radix acc digit : ℕ) : ℕ := 3 * radix * acc + 8 * acc + 3 * digit + 13

/-- A concrete Horner execution. Caller hypotheses identify the finite code,
not an assumed execution or arithmetic oracle. -/
theorem radixStepTrace (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : ℕ)
    (operandRadix : base (slots 0) = encodeWord radix)
    (operandAcc : base (slots 1) = encodeWord acc)
    (operandDigit : base (slots 2) = encodeWord digit)
    (counterEmpty : base (slots 4) = []) (scratchEmpty : base (slots 5) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps radix acc digit]
      (some ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ := by
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  have h24 : slots 2 ≠ slots 4 := slots.injective.ne (by decide)
  have h25 : slots 2 ≠ slots 5 := slots.injective.ne (by decide)
  have h34 : slots 3 ≠ slots 4 := slots.injective.ne (by decide)
  have h53 : slots 5 ≠ slots 3 := slots.injective.ne (by decide)
  have h45 : slots 4 ≠ slots 5 := slots.injective.ne (by decide)
  let multiplied := resultTapes slots base (radix * acc)
  have hmul : (MachineComposition.advance (TM2.step p))^[MachineUnaryMultiply.steps radix acc]
      (some ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .digitDrain), ((ambient, ()), none), multiplied⟩ := by
    have h := MachineUnaryMultiply.multiplyTrace (multiplySlots slots)
      (fun l => labels (.multiply l)) (some (labels .digitDrain)) p
      (fun l => atLabels (.multiply l)) base radix acc operandRadix operandAcc
      counterEmpty scratchEmpty ambient register
    simpa only [MachineUnaryMultiply.resultTapes, multiplySlots_two, multiplied, resultTapes] using h
  have hmulDigit : multiplied (slots 2) = encodeWord digit := by
    simp [multiplied, resultTapes, h23, operandDigit]
  have hmulCounter : multiplied (slots 4) = [] := by
    simp [multiplied, resultTapes, Ne.symm h34, counterEmpty]
  have hmulScratch : multiplied (slots 5) = [] := by
    simp [multiplied, resultTapes, h53, scratchEmpty]
  let copied := Function.update multiplied (slots 4) (encodeWord digit)
  have hcopy : (MachineComposition.advance (TM2.step p))^[2 * (digit + 2)]
      (some ⟨some (labels .digitDrain), ((ambient, ()), none), multiplied⟩) =
      some ⟨some (labels .add), ((ambient, ()), none), copied⟩ := by
    have h := MachineCopy.copyTrace (slots 2) (slots 4) (slots 5) h24 h25 h45 false
      (labels .digitDrain) (labels .digitFork) (some (labels .add)) p
      (atLabels .digitDrain) (atLabels .digitFork) multiplied hmulScratch (ambient, ()) none
    simpa only [copied, hmulDigit, hmulCounter, List.append_nil, encodeWord,
      List.length_append, List.length_replicate, List.length_singleton,
      Nat.add_assoc, Nat.reduceAdd] using h
  have hcopiedCounter : copied (slots 4) = encodeWord digit ++ [] := by simp [copied]
  have hcopiedOutput : copied (slots 3) = encodeWord (radix * acc) ++ base (slots 3) := by
    simp [copied, multiplied, resultTapes, h34]
  let added := MachineUnaryAddAt.unaryTapes (slots 4) (slots 3) copied
    0 (digit + radix * acc) [] (base (slots 3))
  have hadd : (MachineComposition.advance (TM2.step p))^[digit + 1]
      (some ⟨some (labels .add), ((ambient, ()), none), copied⟩) =
      some ⟨some (labels .finish), ((ambient, ()), none), added⟩ :=
    MachineUnaryAddAt.addFromTapes (slots 4) (slots 3) (Ne.symm h34)
      (labels .add) (some (labels .finish)) p (atLabels .add) copied digit (radix * acc)
      [] (base (slots 3)) hcopiedCounter hcopiedOutput (ambient, ()) none
  have hfinishTapes : Function.update added (slots 4) ((added (slots 4)).tail) =
      resultTapes slots base (radix * acc + digit) := by
    funext k
    by_cases hk3 : k = slots 3
    · subst k
      simp only [Function.update_of_ne h34, added, MachineUnaryAddAt.unaryTapes_destination,
        resultTapes_output]
      rw [Nat.add_comm digit (radix * acc)]
    · by_cases hk4 : k = slots 4
      · subst k
        simp [added, MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
          resultTapes, encodeWord, Ne.symm h34, counterEmpty]
      · simp [added, MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
          copied, multiplied, resultTapes, hk3, hk4]
  have hfinish : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .finish), ((ambient, ()), none), added⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ := by
    change some (TM2.stepAux (p (labels .finish)) ((ambient, ()), none) added) = _
    rw [atLabels .finish]
    have hcfg := congrArg (fun tapes => some (⟨exit, ((ambient, ()), none), tapes⟩ :
      TM2.Cfg (Alphabet (K := K)) Λ (State σ))) hfinishTapes
    cases exit <;> simpa only [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt] using hcfg
  rw [show steps radix acc digit =
      1 + ((digit + 1) + (2 * (digit + 2) + MachineUnaryMultiply.steps radix acc)) by
        unfold steps MachineUnaryMultiply.steps; ring]
  rw [Function.iterate_add_apply _ 1,
    Function.iterate_add_apply _ (digit + 1),
    Function.iterate_add_apply _ (2 * (digit + 2)), hmul, hcopy, hadd]
  exact hfinish

def radixStepInTime (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : ℕ)
    (operandRadix : base (slots 0) = encodeWord radix)
    (operandAcc : base (slots 1) = encodeWord acc)
    (operandDigit : base (slots 2) = encodeWord digit)
    (counterEmpty : base (slots 4) = []) (scratchEmpty : base (slots 5) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩)
      (steps radix acc digit) where
  steps := steps radix acc digit
  evals_in_steps := radixStepTrace slots labels exit p atLabels base radix acc digit
    operandRadix operandAcc operandDigit counterEmpty scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

noncomputable def timePolynomial : Polynomial ℕ :=
  Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 11 * Polynomial.X + Polynomial.C 13

theorem steps_le_timePolynomial (radix acc digit : ℕ) :
    steps radix acc digit ≤ timePolynomial.eval (radix + acc + digit + 3) := by
  have hr : radix ≤ radix + acc + digit + 3 := by omega
  have ha : acc ≤ radix + acc + digit + 3 := by omega
  have hd : digit ≤ radix + acc + digit + 3 := by omega
  have hprod := Nat.mul_le_mul hr ha
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  unfold steps
  nlinarith

theorem programTrace (slots : Fin 6 ↪ K) (base : K → List Bool) (radix acc digit : ℕ)
    (operandRadix : base (slots 0) = encodeWord radix)
    (operandAcc : base (slots 1) = encodeWord acc)
    (operandDigit : base (slots 2) = encodeWord digit)
    (counterEmpty : base (slots 4) = []) (scratchEmpty : base (slots 5) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program (σ := σ) slots)))^[steps radix acc digit]
      (some ⟨some (.multiply .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨none, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ :=
  radixStepTrace slots id none (program slots) (fun _ => rfl) base radix acc digit
    operandRadix operandAcc operandDigit counterEmpty scratchEmpty ambient register

def programInPolynomialTime (slots : Fin 6 ↪ K) (base : K → List Bool) (radix acc digit : ℕ)
    (operandRadix : base (slots 0) = encodeWord radix)
    (operandAcc : base (slots 1) = encodeWord acc)
    (operandDigit : base (slots 2) = encodeWord digit)
    (counterEmpty : base (slots 4) = []) (scratchEmpty : base (slots 5) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ) slots))
      ⟨some (.multiply .copyDrain), ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩)
      (timePolynomial.eval
        ((encodeWord radix).length + (encodeWord acc).length + (encodeWord digit).length)) where
  steps := steps radix acc digit
  evals_in_steps := programTrace slots base radix acc digit operandRadix operandAcc operandDigit
    counterEmpty scratchEmpty ambient register
  steps_le_m := by
    have hlength : (encodeWord radix).length + (encodeWord acc).length + (encodeWord digit).length =
        radix + acc + digit + 3 := by
      simp only [encodeWord, List.length_append, List.length_replicate, List.length_singleton]
      omega
    rw [hlength]
    exact steps_le_timePolynomial radix acc digit

end MaxCutGames.Foundations.Complexity.MachineRadixStep

end OAI
