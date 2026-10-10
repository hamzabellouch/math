import Mathlib.Data.List.FinRange
import OAI.Computability.PerfectCompleteness.Foundations.TupleIndexEmitterLemmas

namespace OAI


namespace PerfectCompleteness.TupleInitializationMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

def clean (ambient : σ) : State σ := (ambient, none)

inductive Label
  | seed
  | scan
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seed, .scan]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def prefixOn (destinations : List K) (addedBits : List Bool) (base : K → List Bool) :
    K → List Bool :=
  fun k => if k ∈ destinations then addedBits ++ base k else base k

@[simp] theorem prefixOn_nil (destinations : List K) (base : K → List Bool) :
    prefixOn destinations [] base = base := by
  funext k
  simp [prefixOn]

theorem prefixOn_comp (destinations : List K) (first second : List Bool)
    (base : K → List Bool) :
    prefixOn destinations first (prefixOn destinations second base) =
      prefixOn destinations (first ++ second) base := by
  funext k
  by_cases hk : k ∈ destinations <;> simp [prefixOn, hk, List.append_assoc]

theorem prefixOn_update (destinations : List K) (src : K)
    (hsrc : src ∉ destinations) (addedBits rest : List Bool) (base : K → List Bool) :
    prefixOn destinations addedBits (Function.update base src rest) =
      Function.update (prefixOn destinations addedBits base) src rest := by
  funext k
  by_cases hk : k = src
  · subst k
    simp [prefixOn, hsrc]
  · simp [prefixOn, hk]

def pushEach (destinations : List K) (bit : Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  match destinations with
  | [] => next
  | dst :: rest => .push dst (fun _ => bit) (pushEach rest bit next)

theorem stepAux_pushEach (destinations : List K) (hn : destinations.Nodup) (bit : Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (state : State σ) (tapes : K → List Bool) :
    TM2.stepAux (pushEach destinations bit next) state tapes =
      TM2.stepAux next state (prefixOn destinations [bit] tapes) := by
  induction destinations generalizing tapes with
  | nil =>
    have emptyDest : prefixOn [] [bit] tapes = tapes := by
      funext k
      simp [prefixOn]
    simp only [pushEach, emptyDest]
  | cons dst rest ih =>
    obtain ⟨hdst, hrest⟩ := List.nodup_cons.mp hn
    simp only [pushEach, TM2.stepAux]
    rw [ih hrest]
    apply congrArg (TM2.stepAux next state)
    funext k
    by_cases hk : k = dst
    · subst k
      simp [prefixOn, hdst]
    · simp [prefixOn, hk]

omit [DecidableEq K] in
theorem pushEach_pushBound (destinations : List K) (bit : Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ)) :
    Runtime.statementPushBound (pushEach destinations bit next) =
      destinations.length + Runtime.statementPushBound next := by
  induction destinations with
  | nil => simp [pushEach]
  | cons dst rest ih =>
    simp only [pushEach, Runtime.statementPushBound, ih, List.length_cons]
    omega

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .load (fun state => clean state.1)
    (match exit with | none => .halt | some label => .goto (fun _ => label))

theorem stepAux_finish (exit : Option Λ) (ambient : σ) (register : Option Bool)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) (ambient, register) tapes = ⟨exit, clean ambient, tapes⟩ := by
  cases exit <;> rfl

omit [DecidableEq K] in
@[simp] theorem finish_pushBound (exit : Option Λ) :
    Runtime.statementPushBound (finish (K := K) (σ := σ) exit) = 0 := by
  cases exit <;> rfl

def instruction (src : K) (currents remaining : List K)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .seed => pushEach (currents ++ remaining) false
      (.pop src (fun state _ => clean state.1) (.goto (fun _ => labels .scan)))
  | .scan => .pop src (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (pushEach remaining true (finish (some (labels .scan)))) (finish exit))

omit [DecidableEq K] in
theorem instruction_pushBound (src : K) (currents remaining : List K)
    (labels : Label → Λ) (exit : Option Λ) (label : Label) :
    Runtime.statementPushBound (instruction (σ := σ) src currents remaining labels exit label) ≤
      currents.length + remaining.length := by
  cases label with
  | seed =>
    simp [instruction, pushEach_pushBound, Runtime.statementPushBound]
  | scan =>
    change max
      (Runtime.statementPushBound
        (pushEach remaining true (finish (K := K) (σ := σ) (some (labels .scan)))))
      (Runtime.statementPushBound (finish (K := K) (σ := σ) exit)) ≤ _
    rw [pushEach_pushBound, finish_pushBound, finish_pushBound]
    omega

theorem scanStep_false (src : K) (currents remaining : List K)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program (labels .scan) = instruction src currents remaining labels exit .scan)
    (base : K → List Bool) (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (labels .scan), (ambient, register), Function.update base src (false :: suffix)⟩ =
    some ⟨exit, clean ambient, Function.update base src suffix⟩ := by
  change some (TM2.stepAux (program (labels .scan)) _ _) = _
  rw [atScan]
  cases exit <;> simp [instruction, TM2.stepAux, finish, clean]

theorem scanStep_true (src : K) (currents remaining : List K)
    (hn : remaining.Nodup) (hsrc : src ∉ remaining)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program (labels .scan) = instruction src currents remaining labels exit .scan)
    (base : K → List Bool) (rest : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (labels .scan), (ambient, register), Function.update base src (true :: rest)⟩ =
    some ⟨some (labels .scan), clean ambient,
      Function.update (prefixOn remaining [true] base) src rest⟩ := by
  change some (TM2.stepAux (program (labels .scan)) _ _) = _
  rw [atScan]
  simp only [instruction, TM2.stepAux.eq_3, TM2.stepAux.eq_5, Function.update_self,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true, Function.update_idem]
  rw [stepAux_pushEach remaining hn, stepAux_finish,
    prefixOn_update remaining src hsrc]

theorem scanTrace (src : K) (currents remaining : List K)
    (hn : remaining.Nodup) (hsrc : src ∉ remaining)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program (labels .scan) = instruction src currents remaining labels exit .scan)
    (base : K → List Bool) (count : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[count + 1]
      (some ⟨some (labels .scan), (ambient, register),
        Function.update base src (encodeWord count ++ suffix)⟩) =
    some ⟨exit, clean ambient,
      Function.update (prefixOn remaining (List.replicate count true) base) src suffix⟩ := by
  induction count generalizing base register with
  | zero =>
    simpa [encodeWord] using
      scanStep_false src currents remaining labels exit program atScan base suffix ambient register
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    change (advance (TM2.step program))^[count + 1]
      (TM2.step program ⟨some (labels .scan), (ambient, register),
        Function.update base src (encodeWord (count + 1) ++ suffix)⟩) = _
    rw [show encodeWord (count + 1) ++ suffix =
      true :: (encodeWord count ++ suffix) by
        simp [encodeWord, List.replicate_succ, List.append_assoc]]
    rw [scanStep_true src currents remaining hn hsrc labels exit program atScan]
    change (advance (TM2.step program))^[count + 1]
      (some ⟨some (labels .scan), (ambient, none),
        Function.update (prefixOn remaining [true] base) src (encodeWord count ++ suffix)⟩) = _
    rw [ih, prefixOn_comp]
    simp only [List.replicate_succ']

theorem seedStep (src : K) (currents remaining : List K)
    (hn : (currents ++ remaining).Nodup) (hsrc : src ∉ currents ++ remaining)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atSeed : program (labels .seed) = instruction src currents remaining labels exit .seed)
    (base : K → List Bool) (rest : List Bool) (ambient : σ) (register : Option Bool)
    (sourceWord : base src = true :: rest) :
    TM2.step program ⟨some (labels .seed), (ambient, register), base⟩ =
      some ⟨some (labels .scan), clean ambient,
        Function.update (prefixOn (currents ++ remaining) [false] base) src rest⟩ := by
  change some (TM2.stepAux (program (labels .seed)) _ _) = _
  rw [atSeed]
  simp only [instruction]
  rw [stepAux_pushEach (currents ++ remaining) hn]
  simp [TM2.stepAux, prefixOn, hsrc, sourceWord, clean]

def initializedTapes (src : K) (currents remaining : List K) (base : K → List Bool)
    (last : Nat) (suffix : List Bool) : K → List Bool :=
  Function.update
    (prefixOn remaining (List.replicate last true)
      (prefixOn (currents ++ remaining) [false] base)) src suffix

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem initializeTrace (src : K) (currents remaining : List K)
    (hn : (currents ++ remaining).Nodup) (hsrc : src ∉ currents ++ remaining)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction src currents remaining labels exit label)
    (base : K → List Bool) (ambient : σ) (m : Nat) (hm : 0 < m) (suffix : List Bool)
    (sourceWord : base src = encodeWord m ++ suffix) :
    (advance (TM2.step program))^[m + 1]
      (some ⟨some (labels .seed), clean ambient, base⟩) =
      some ⟨exit, clean ambient, initializedTapes src currents remaining base (m - 1) suffix⟩ := by
  have hrem : remaining.Nodup := (List.nodup_append.mp hn).2.1
  have hsrem : src ∉ remaining := fun h => hsrc (List.mem_append_right _ h)
  cases m with
  | zero => omega
  | succ n =>
    have first : (advance (TM2.step program))^[1]
        (some ⟨some (labels .seed), clean ambient, base⟩) =
        some ⟨some (labels .scan), clean ambient,
          Function.update (prefixOn (currents ++ remaining) [false] base) src
            (encodeWord n ++ suffix)⟩ := by
      rw [Function.iterate_one, advance_some]
      apply seedStep src currents remaining hn hsrc labels exit program (atLabels .seed)
      simpa [encodeWord, List.replicate_succ, List.append_assoc] using sourceWord
    have rest := scanTrace src currents remaining hrem hsrem labels exit program (atLabels .scan)
      (prefixOn (currents ++ remaining) [false] base) n suffix ambient none
    have joined := joinTrace first rest
    rw [show 1 + (n + 1) = n + 1 + 1 by omega] at joined
    simpa only [initializedTapes, Nat.add_sub_cancel] using joined

def initializeInTime (src : K) (currents remaining : List K)
    (hn : (currents ++ remaining).Nodup) (hsrc : src ∉ currents ++ remaining)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction src currents remaining labels exit label)
    (base : K → List Bool) (ambient : σ) (m : Nat) (hm : 0 < m) (suffix : List Bool)
    (sourceWord : base src = encodeWord m ++ suffix) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .seed), clean ambient, base⟩
      (some ⟨exit, clean ambient, initializedTapes src currents remaining base (m - 1) suffix⟩)
      (m + 1) where
  steps := m + 1
  evals_in_steps := initializeTrace src currents remaining hn hsrc labels exit program atLabels
    base ambient m hm suffix sourceWord
  steps_le_m := Nat.le_refl _

@[simp] theorem initializedTapes_source (src : K) (currents remaining : List K)
    (base : K → List Bool) (last : Nat) (suffix : List Bool) :
    initializedTapes src currents remaining base last suffix src = suffix := by
  simp [initializedTapes]

theorem initializedTapes_current (src : K) (currents remaining : List K)
    (base : K → List Bool) (last : Nat) (suffix : List Bool) (k : K)
    (hcurrent : k ∈ currents) (hremaining : k ∉ remaining) (hsrc : k ≠ src)
    (hempty : base k = []) :
    initializedTapes src currents remaining base last suffix k = encodeWord 0 := by
  simp [initializedTapes, prefixOn, hcurrent, hremaining, hsrc, hempty, encodeWord]

theorem initializedTapes_remaining (src : K) (currents remaining : List K)
    (base : K → List Bool) (last : Nat) (suffix : List Bool) (k : K)
    (hremaining : k ∈ remaining) (hsrc : k ≠ src) (hempty : base k = []) :
    initializedTapes src currents remaining base last suffix k = encodeWord last := by
  simp [initializedTapes, prefixOn, hremaining, hsrc, hempty, encodeWord]

theorem initializedTapes_frame (src : K) (currents remaining : List K)
    (base : K → List Bool) (last : Nat) (suffix : List Bool) (k : K)
    (hcurrent : k ∉ currents) (hremaining : k ∉ remaining) (hsrc : k ≠ src) :
    initializedTapes src currents remaining base last suffix k = base k := by
  simp [initializedTapes, prefixOn, hcurrent, hremaining, hsrc]

section Arena

variable {width : Nat} {Extra : Type}

abbrev Arena (width : Nat) (Extra : Type) := TupleIndexEmitter.Tape width (Fin width ⊕ Extra)

def currentDestinations (width : Nat) (Extra : Type) : List (Arena width Extra) :=
  List.ofFn (fun i : Fin width => TupleIndexEmitter.Tape.current i)

def remainingDestinations (width : Nat) (Extra : Type) : List (Arena width Extra) :=
  List.ofFn (fun i : Fin width => TupleIndexEmitter.Tape.extra (Sum.inl i))

theorem destinations_nodup (width : Nat) (Extra : Type) :
    (currentDestinations width Extra ++ remainingDestinations width Extra).Nodup := by
  unfold currentDestinations remainingDestinations
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply List.nodup_ofFn.mpr
    intro i j h
    simpa using h
  · apply List.nodup_ofFn.mpr
    intro i j h
    simpa using h
  · intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    intro h
    cases h

theorem source_not_destination (src : Extra) :
    (TupleIndexEmitter.Tape.extra (Sum.inr src) : Arena width Extra) ∉
      currentDestinations width Extra ++ remainingDestinations width Extra := by
  simp [currentDestinations, remainingDestinations, List.mem_ofFn]

variable [DecidableEq Extra]

def arenaInstruction (src : Extra) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : Arena width Extra => Bool) Λ (State σ) :=
  instruction (.extra (.inr src)) (currentDestinations width Extra)
    (remainingDestinations width Extra) labels exit

omit [DecidableEq Extra] in
theorem arenaInstruction_pushBound (src : Extra) (labels : Label → Λ) (exit : Option Λ)
    (label : Label) :
    Runtime.statementPushBound (arenaInstruction (width := width) (σ := σ) src labels exit label) ≤
      2 * width := by
  simpa only [arenaInstruction, currentDestinations, remainingDestinations,
    List.length_ofFn, two_mul] using
    instruction_pushBound (σ := σ) (.extra (.inr src) : Arena width Extra)
      (currentDestinations width Extra) (remainingDestinations width Extra) labels exit label

def arenaInitializedTapes (src : Extra) (base : Arena width Extra → List Bool)
    (last : Nat) (suffix : List Bool) : Arena width Extra → List Bool :=
  initializedTapes (.extra (.inr src)) (currentDestinations width Extra)
    (remainingDestinations width Extra) base last suffix

@[simp] theorem arenaInitializedTapes_source (src : Extra)
    (base : Arena width Extra → List Bool) (last : Nat) (suffix : List Bool) :
    arenaInitializedTapes src base last suffix (.extra (.inr src)) = suffix := by
  simp [arenaInitializedTapes]

theorem arenaInitializedTapes_current (src : Extra) (base : Arena width Extra → List Bool)
    (last : Nat) (suffix : List Bool) (i : Fin width) (hempty : base (.current i) = []) :
    arenaInitializedTapes src base last suffix (.current i) = encodeWord 0 := by
  simp [arenaInitializedTapes, initializedTapes, prefixOn, currentDestinations,
    remainingDestinations, List.mem_ofFn, hempty, encodeWord]

theorem arenaInitializedTapes_remaining (src : Extra) (base : Arena width Extra → List Bool)
    (last : Nat) (suffix : List Bool) (i : Fin width)
    (hempty : base (.extra (.inl i)) = []) :
    arenaInitializedTapes src base last suffix (.extra (.inl i)) = encodeWord last := by
  simp [arenaInitializedTapes, initializedTapes, prefixOn, currentDestinations,
    remainingDestinations, List.mem_ofFn, hempty, encodeWord]

@[simp] theorem arenaInitializedTapes_scratch (src : Extra)
    (base : Arena width Extra → List Bool) (last : Nat) (suffix : List Bool) :
    arenaInitializedTapes src base last suffix .scratch = base .scratch := by
  simp [arenaInitializedTapes, initializedTapes, prefixOn, currentDestinations,
    remainingDestinations, List.mem_ofFn]

@[simp] theorem arenaInitializedTapes_output (src : Extra)
    (base : Arena width Extra → List Bool) (last : Nat) (suffix : List Bool) :
    arenaInitializedTapes src base last suffix .output = base .output := by
  simp [arenaInitializedTapes, initializedTapes, prefixOn, currentDestinations,
    remainingDestinations, List.mem_ofFn]

theorem arenaInitializedTapes_other (src x : Extra) (hx : x ≠ src)
    (base : Arena width Extra → List Bool) (last : Nat) (suffix : List Bool) :
    arenaInitializedTapes src base last suffix (.extra (.inr x)) = base (.extra (.inr x)) := by
  simp [arenaInitializedTapes, initializedTapes, prefixOn, currentDestinations,
    remainingDestinations, List.mem_ofFn, hx]

def arenaInitializeInTime (src : Extra) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : Arena width Extra => Bool) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = arenaInstruction src labels exit label)
    (base : Arena width Extra → List Bool) (ambient : σ)
    (m : Nat) (hm : 0 < m) (suffix : List Bool)
    (sourceWord : base (.extra (.inr src)) = encodeWord m ++ suffix) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .seed), clean ambient, base⟩
      (some ⟨exit, clean ambient, arenaInitializedTapes src base (m - 1) suffix⟩) (m + 1) :=
  initializeInTime (K := Arena width Extra) (.extra (.inr src)) (currentDestinations width Extra)
    (remainingDestinations width Extra) (destinations_nodup width Extra)
    (source_not_destination src) labels exit program
    (fun label => by simpa only [arenaInstruction] using atLabels label)
    base ambient m hm suffix sourceWord

omit [DecidableEq Extra] in
theorem arena_finite [Fintype Extra] : Finite (Arena width Extra) := inferInstance

end Arena

end PerfectCompleteness.TupleInitializationMachine

end OAI
