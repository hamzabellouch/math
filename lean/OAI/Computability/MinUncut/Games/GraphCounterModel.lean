import Mathlib
import OAI.Computability.MinUncut.Machines.MachineLazyTableRuntime

namespace OAI

namespace MinUncutGames.Foundations.Complexity.GraphCounterModel

open Turing

inductive ExtraTape where
  | input | archive | scratch | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.input, .archive, .scratch, .output]

protected theorem ExtraTape.enumList_getElem?_ctorIdx_eq (x : ExtraTape) :
    ExtraTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive ExtraLabel where
  | copyFirst | copySecond | seed | headerFirst | headerSecond
  | clearInput | clockCopy | archiveCopy | finalReverse
  deriving DecidableEq

protected abbrev ExtraLabel.enumList : List ExtraLabel := [.copyFirst, .copySecond, .seed,
  .headerFirst, .headerSecond, .clearInput, .clockCopy, .archiveCopy, .finalReverse]

protected theorem ExtraLabel.enumList_getElem?_ctorIdx_eq (x : ExtraLabel) :
    ExtraLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ExtraLabel.enumList_nodup : ExtraLabel.enumList.Nodup := by decide

instance : Fintype ExtraLabel where
  elems := ⟨ExtraLabel.enumList, ExtraLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 3 ⊕ ExtraTape
abbrev Label := Fin 5 ⊕ ExtraLabel
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineLogCounter.State × Option Bool

def initialState : State := (MachineLogCounter.initialState, none)

def clockLabel : Option (Fin 5) → Option Label
  | none => some (.inr .clearInput)
  | some l => some (.inl l)

def clockStatement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State →
    TM2.Stmt Alphabet Label State
  | .push k f next => .push (.inl k) (fun state => f state.1) (clockStatement next)
  | .peek k f next => .peek (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .pop k f next => .pop (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (clockStatement next)
  | .branch f yes no => .branch (fun state => f state.1) (clockStatement yes) (clockStatement no)
  | .goto f => .goto (fun state => .inl (f state.1))
  | .halt => .goto (fun _ => .inr .clearInput)

def readHeader (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop (.inr .input) (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push (.inl 0) (fun _ => true) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def program : Label → TM2.Stmt Alphabet Label State
  | .inl l => clockStatement (MachineLogCounter.program l)
  | .inr .copyFirst => Reduction.MachineTransfer.loopAt (.inr .input) (.inr .scratch)
      id false (.inr .copyFirst) (some (.inr .copySecond))
  | .inr .copySecond => MachineCopy.forkLoop (.inr .scratch) (.inr .input) (.inr .archive)
      false (.inr .copySecond) (some (.inr .seed))
  | .inr .seed => .push (.inl 0) (fun _ => false) (.goto fun _ => .inr .headerFirst)
  | .inr .headerFirst => readHeader (.inr .headerFirst) (.inr .headerSecond)
  | .inr .headerSecond => readHeader (.inr .headerSecond) (.inl 0)
  | .inr .clearInput => MachineDrain.drain (.inr .input) (.inr .clearInput)
      (some (.inr .clockCopy))
  | .inr .clockCopy => Reduction.MachineTransfer.loopAt (.inl 2) (.inr .scratch)
      id false (.inr .clockCopy) (some (.inr .archiveCopy))
  | .inr .archiveCopy => Reduction.MachineTransfer.loopAt (.inr .archive) (.inr .scratch)
      id false (.inr .archiveCopy) (some (.inr .finalReverse))
  | .inr .finalReverse => Reduction.MachineTransfer.loopAt (.inr .scratch) (.inr .output)
      id false (.inr .finalReverse) none

def machine : FinTM2 where
  K := Tape
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := Alphabet
  Λ := Label
  main := .inr .copyFirst
  σ := State
  initialState := initialState
  m := program

def clockTapes (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool) : Tape → List Bool
  | .inl k => tapes k
  | .inr k => extra k

def clockConfiguration (extra : ExtraTape → List Bool) (register : Option Bool)
    (c : TM2.Cfg MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State) :
    TM2.Cfg Alphabet Label State := ⟨clockLabel c.l, (c.var, register), clockTapes c.stk extra⟩

theorem clockTapes_update (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool)
    (k : Fin 3) (word : List Bool) :
    clockTapes (Function.update tapes k word) extra =
      Function.update (clockTapes tapes extra) (.inl k) word := by
  funext tape
  cases tape <;> simp [clockTapes, Function.comp_def]

theorem clockStatement_simulation (extra : ExtraTape → List Bool) (register : Option Bool)
    (statement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State)
    (state : MachineLogCounter.State) (tapes : Fin 3 → List Bool) :
    TM2.stepAux (clockStatement statement) (state, register) (clockTapes tapes extra) =
      clockConfiguration extra register (TM2.stepAux statement state tapes) := by
  induction statement generalizing state tapes with
  | push k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [clockStatement, TM2.stepAux, clockTapes] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [clockStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

theorem clockStep (extra : ExtraTape → List Bool) (register : Option Bool)
    (a b : MachineLogCounter.machine.Cfg)
    (h : MachineLogCounter.machine.step a = some b) :
    TM2.step program (clockConfiguration extra register a) =
      some (clockConfiguration extra register b) := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => cases h
      | some label =>
          have hb := Option.some.inj h
          subst b
          exact congrArg some (clockStatement_simulation extra register
            (MachineLogCounter.program label) state tapes)

def clockInTime (extra : ExtraTape → List Bool) (register : Option Bool) (n : Nat) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration extra register (initList MachineLogCounter.machine (encodeWord n)))
      (some (clockConfiguration extra register
        (haltList MachineLogCounter.machine (encodeWord (n.log2 + 1))))) (8 * n + 4) :=
  MachineComposition.liftExecutionInTime _ _ (clockConfiguration extra register)
    (clockStep extra register) (MachineLogCounter.outputsInTime n)

open Turing

def startExtra (input archive : List Bool) : ExtraTape → List Bool
  | .input => input
  | .archive => archive
  | _ => []

def startMemory (input archive sum : List Bool) : Tape → List Bool
  | .inl k => if k = 0 then sum else []
  | .inr k => startExtra input archive k

theorem startMemory_input_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inr .input) replacement =
      startMemory replacement archive sum := by
  funext tape
  cases tape with
  | inl k => simp [startMemory]
  | inr k => cases k <;> simp [startMemory, startExtra]

theorem startMemory_sum_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inl 0) replacement =
      startMemory input archive replacement := by
  funext tape
  cases tape with
  | inl k => by_cases h : k = 0 <;> simp [startMemory, h]
  | inr k => simp [startMemory]

theorem headerStep_zero (again next : Label)
    (atHeader : program again = readHeader again next)
    (suffix archive : List Bool) (sum : Nat)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register), startMemory (encodeWord 0 ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord sum)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_zero, List.nil_append, List.singleton_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_false]
  rw [startMemory_input_update]

theorem headerStep_succ (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register),
        startMemory (encodeWord (n + 1) ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some again, (state, some true),
        startMemory (encodeWord n ++ suffix) archive (encodeWord (sum + 1))⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
    Option.getD_some, Bool.cond_true]
  rw [startMemory_input_update, startMemory_sum_update]
  rfl

theorem headerTrace (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (state, register),
        startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩) =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩ := by
  induction n generalizing sum register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
        headerStep_zero again next atHeader suffix archive sum state register
  | succ n ih =>
      rw [Function.iterate_succ_apply, MachineComposition.advance_some]
      rw [headerStep_succ again next atHeader n sum suffix archive state register]
      simpa only [Nat.add_assoc, Nat.add_comm 1 sum] using ih (sum + 1) (some true)

def headerInTime (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (state, register), startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩
      (some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := headerTrace again next atHeader n sum suffix archive state register
  steps_le_m := le_rfl

theorem initialMemory (word : List Bool) :
    initList machine word =
      ⟨some (.inr .copyFirst), initialState, startMemory word [] []⟩ := by
  have ht : (initList machine word).stk = startMemory word [] [] := by
    funext tape
    cases tape with
    | inl k => simp [initList, machine, startMemory]
    | inr k =>
      cases k <;> simp [initList, machine, startMemory, startExtra]
      all_goals rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem clockInitialMemory (word rest : List Bool) (sum : Nat) :
    clockConfiguration (startExtra rest word) none
      (initList MachineLogCounter.machine (encodeWord sum)) =
      ⟨some (.inl 0), initialState, startMemory rest word (encodeWord sum)⟩ := by
  have ht : clockTapes (initList MachineLogCounter.machine (encodeWord sum)).stk
      (startExtra rest word) = startMemory rest word (encodeWord sum) := by
    funext tape
    cases tape with
    | inl k =>
      fin_cases k <;> simp [clockTapes, initList, MachineLogCounter.machine, startMemory]
      all_goals rfl
    | inr k => rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

def startInTime (n m : Nat) (rest : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (encodeWords [n, m] ++ rest))
      (some (clockConfiguration (startExtra rest (encodeWords [n, m] ++ rest)) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * ((encodeWords [n, m] ++ rest).length + 1) + 1 + (n + 1) + (m + 1)) := by
  let word := encodeWords [n, m] ++ rest
  let b₀ := startMemory word [] []
  let b₁ := startMemory word word []
  let b₂ := startMemory word word (encodeWord 0)
  have hc : Function.update b₀ (.inr .archive) (b₀ (.inr .input) ++ b₀ (.inr .archive)) = b₁ := by
    funext tape
    cases tape with
    | inl k => simp [b₀, b₁, startMemory]
    | inr k => cases k <;> simp [b₀, b₁, startMemory, startExtra]
  let copy := MachineCopy.copyInTime (.inr ExtraTape.input) (.inr ExtraTape.archive)
    (.inr ExtraTape.scratch) (by decide) (by decide) (by decide) false
    (.inr ExtraLabel.copyFirst) (.inr ExtraLabel.copySecond) (some (.inr ExtraLabel.seed))
    program rfl rfl b₀ rfl MachineLogCounter.initialState none
  have copy' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .copyFirst), initialState, b₀⟩
      (some ⟨some (.inr .seed), initialState, b₁⟩) (2 * (word.length + 1)) := by
    have h := copy
    rw [hc] at h
    simpa only [initialState, show b₀ (.inr .input) = word from rfl] using h
  have seed : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .seed), initialState, b₁⟩
      (some ⟨some (.inr .headerFirst), initialState, b₂⟩) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change some (TM2.stepAux (program (.inr .seed)) initialState b₁) = _
    simp only [program, TM2.stepAux, b₁, startMemory]
    rw [startMemory_sum_update]
    rfl
  have first := headerInTime (.inr .headerFirst) (.inr .headerSecond) rfl
    n 0 (encodeWord m ++ rest) word MachineLogCounter.initialState none
  have first' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerFirst), initialState, b₂⟩
      (some ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩) (n + 1) := by
    simpa only [b₂, initialState, word, encodeWords, List.append_nil, List.append_assoc,
      Nat.add_zero] using first
  have second := headerInTime (.inr .headerSecond) (.inl 0) rfl
    m n rest word MachineLogCounter.initialState none
  have second' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩
      (some ⟨some (.inl 0), initialState, startMemory rest word (encodeWord (n + m))⟩)
      (m + 1) := by simpa only [initialState, Nat.add_comm m n] using second
  let p₀ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copy' seed
  let p₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ first'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₁ second'
  rw [initialMemory, clockInitialMemory]
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change p.steps ≤ 2 * (word.length + 1) + 1 + (n + 1) + (m + 1)
      omega
  }

end MinUncutGames.Foundations.Complexity.GraphCounterModel

namespace MinUncutGames.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

def extraTapes (rest original : List Bool) : ExtraTape → List Bool
  | .input => rest
  | .archive => original
  | _ => []

def frame (input archive counter reversed output : List Bool) : Tape → List Bool
  | .inl i => if i = 2 then counter else []
  | .inr .input => input
  | .inr .archive => archive
  | .inr .scratch => reversed
  | .inr .output => output

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem start_eq (counter rest original : List Bool) :
    clockConfiguration (extraTapes rest original) none
      (haltList MachineLogCounter.machine counter) =
      ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩ := by
  rw [MachineLogCounter.haltList_eq]
  unfold clockConfiguration
  congr 1
  funext tape
  cases tape with
  | inl i => fin_cases i <;> simp [clockTapes, frame, MachineLogCounter.configuration,
      MachineLogCounter.rawTapes]
  | inr k => cases k <;> rfl

theorem finish_eq (word : List Bool) :
    (⟨none, initialState, frame [] [] [] [] word⟩ : TM2.Cfg Alphabet Label State) =
      haltList machine word := by
  unfold haltList
  congr 1
  funext tape
  cases tape with
  | inl i => simp [machine, frame]
  | inr k =>
    cases k <;> simp [machine, frame]
    all_goals rfl

theorem drainTrace (rest original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[rest.length + 1]
      (some ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩) =
      some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩ := by
  have h := (MachineDrain.drainInTime (Sum.inr ExtraTape.input) (Sum.inr ExtraLabel.clearInput)
    (some (.inr .clockCopy)) program rfl (frame rest original counter [] [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[rest.length + 1]
    (some ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩) = _ at h
  have update : Function.update (frame rest original counter [] []) (.inr .input) [] =
      frame [] original counter [] [] := by
    funext tape
    cases tape with
    | inl i => simp [frame]
    | inr k => cases k <;> simp [frame]
  simpa only [update, initialState] using h

theorem clockCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[counter.length + 1]
      (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) =
      some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inl (2 : Fin 3))
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .clockCopy)
    (some (.inr .archiveCopy)) program rfl (frame [] original counter [] [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[counter.length + 1]
    (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inl (2 : Fin 3))
      (Sum.inr ExtraTape.scratch) (frame [] original counter [] []) []
        ((frame [] original counter [] [] (.inl 2)).reverse.map id ++
          frame [] original counter [] [] (.inr .scratch)) =
      frame [] original [] counter.reverse [] := by
    funext tape
    cases tape with
    | inl i => fin_cases i <;> simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem archiveCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + 1]
      (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) =
      some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.archive)
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .archiveCopy)
    (some (.inr .finalReverse)) program rfl (frame [] original [] counter.reverse [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[original.length + 1]
    (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.archive)
      (Sum.inr ExtraTape.scratch) (frame [] original [] counter.reverse []) []
        ((frame [] original [] counter.reverse [] (.inr .archive)).reverse.map id ++
          frame [] original [] counter.reverse [] (.inr .scratch)) =
      frame [] [] [] (original.reverse ++ counter.reverse) [] := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem reverseTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + counter.length + 1]
      (some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩) =
      some (haltList machine (counter ++ original)) := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.scratch)
    (Sum.inr ExtraTape.output) (by decide) id false (.inr .finalReverse) none program rfl
    (frame [] [] [] (original.reverse ++ counter.reverse) []) MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[
    (original.reverse ++ counter.reverse).length + 1]
    (some ⟨some (.inr .finalReverse), initialState,
      frame [] [] [] (original.reverse ++ counter.reverse) []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.scratch)
      (Sum.inr ExtraTape.output) (frame [] [] [] (original.reverse ++ counter.reverse) []) []
        ((frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .scratch)).reverse.map id ++
          frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .output)) =
      frame [] [] [] [] (counter ++ original) := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  rw [update] at h
  rw [← finish_eq]
  simpa only [List.length_append, List.length_reverse, initialState] using! h

theorem finishTrace (counter rest original : List Bool) :
    (MachineComposition.advance (TM2.step program))^[
        rest.length + 2 * counter.length + 2 * original.length + 4]
      (some (clockConfiguration (extraTapes rest original) none
        (haltList MachineLogCounter.machine counter))) =
      some (haltList machine (counter ++ original)) := by
  rw [start_eq]
  have total := trace_trans _
    (trace_trans _ (trace_trans _ (drainTrace rest original counter)
      (clockCopyTrace original counter)) (archiveCopyTrace original counter))
    (reverseTrace original counter)
  simpa only [show rest.length + 1 + (counter.length + 1) + (original.length + 1) +
      (original.length + counter.length + 1) =
      rest.length + 2 * counter.length + 2 * original.length + 4 by omega] using total

def finishInTime (counter rest original : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration (extraTapes rest original) none (haltList MachineLogCounter.machine counter))
      (some (haltList machine (counter ++ original)))
      (rest.length + 2 * counter.length + 2 * original.length + 4) where
  steps := rest.length + 2 * counter.length + 2 * original.length + 4
  evals_in_steps := finishTrace counter rest original
  steps_le_m := le_rfl

end MinUncutGames.Foundations.Complexity.GraphCounterFinish

namespace MinUncutGames.Foundations.Complexity.GraphCounterPrefix

open Turing PCP GraphCounterModel GraphCounterFinish

def rawOutput (n m : Nat) (rest : List Bool) : List Bool :=
  encodeWord ((n + m).log2 + 1) ++ (encodeWords [n, m] ++ rest)

def rawInTime (n m : Nat) (rest : List Bool) :
    TM2OutputsInTime machine (encodeWords [n, m] ++ rest) (some (rawOutput n m rest))
      (20 * (encodeWords [n, m] ++ rest).length + 30) := by
  let original := encodeWords [n, m] ++ rest
  let start := startInTime n m rest
  let clock := clockInTime (extraTapes rest original) none (n + m)
  let finish := finishInTime (encodeWord ((n + m).log2 + 1)) rest original
  have start' : StateTransition.EvalsToInTime (TM2.step program)
      (initList machine original)
      (some (clockConfiguration (extraTapes rest original) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * (original.length + 1) + 1 + (n + 1) + (m + 1)) := start
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start' clock
  let total := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  refine { toEvalsTo := total.toEvalsTo, steps_le_m := ?_ }
  have bound := total.steps_le_m
  have hlog := Nat.log2_le_self (n + m)
  have hlength : original.length = n + m + 2 + rest.length := by
    simp only [original, List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  simp only [encodeWord_length] at bound
  change total.steps ≤ 20 * original.length + 30
  omega

def count (table : GraphTables.Table) : Nat := (table.vertices + table.darts).log2 + 1

def output (table : GraphTables.Table) : List Bool :=
  encodeWord (count table) ++ GraphTables.tableBits table

def rowsBits (table : GraphTables.Table) : List Bool :=
  encodeWords ((GraphTables.rowList table).flatMap GraphTables.rowWords)

theorem tableBits_decomposition (table : GraphTables.Table) :
    GraphTables.tableBits table = encodeWords [table.vertices, table.darts] ++ rowsBits table :=
  encodeWords_append _ _

def outputsInTime (table : GraphTables.Table) :
    TM2OutputsInTime machine (GraphTables.tableBits table) (some (output table))
      (20 * (GraphTables.tableBits table).length + 30) := by
  have run := rawInTime table.vertices table.darts (rowsBits table)
  simpa only [rawOutput, output, count, tableBits_decomposition] using run

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits id output where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 20 * Polynomial.X + 30
  outputsFun table := by
    change TM2OutputsInTime machine ((GraphTables.tableBits table).map id)
      (some ((output table).map id))
      ((20 * Polynomial.X + 30 : Polynomial Nat).eval (GraphTables.tableBits table).length)
    have input_eq : @List.map (machine.Γ machine.k₀) (machine.Γ machine.k₀) id
        (GraphTables.tableBits table) = GraphTables.tableBits table := List.map_id _
    have output_eq : @List.map (machine.Γ machine.k₁) (machine.Γ machine.k₁) id
        (output table) = output table := List.map_id _
    rw [input_eq, output_eq]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using outputsInTime table

end MinUncutGames.Foundations.Complexity.GraphCounterPrefix

end OAI
