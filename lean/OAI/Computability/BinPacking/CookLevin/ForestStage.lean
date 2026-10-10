import Mathlib.Logic.Function.Basic
import OAI.Computability.BinPacking.Computation.MachineExpanderRowDivision
import OAI.Computability.BinPacking.CookLevin.PostfixBounds

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ForestPlacement

open Turing

variable {I J K L Λ σ : Type}

abbrev Tapes (I : Type) := I → List Bool

noncomputable def fill (ports : I ↪ K) (base : Tapes K) (contents : Tapes I) : Tapes K :=
  Function.extend ports contents base

@[simp] theorem fill_at (ports : I ↪ K) (base : Tapes K) (contents : Tapes I) (i : I) :
    fill ports base contents (ports i) = contents i :=
  ports.injective.extend_apply contents base i

theorem fill_other (ports : I ↪ K) (base : Tapes K) (contents : Tapes I) (k : K)
    (outside : ∀ i, ports i ≠ k) : fill ports base contents k = base k :=
  Function.extend_apply' contents base k (not_exists.mpr outside)

theorem fill_self (ports : I ↪ K) (base : Tapes K) :
    fill ports base (fun i => base (ports i)) = base := by
  classical
  funext k
  by_cases h : ∃ i, ports i = k
  · rcases h with ⟨i, rfl⟩
    exact fill_at ports base _ i
  · exact fill_other ports base _ k (not_exists.mp h)

theorem fill_update [DecidableEq I] [DecidableEq K] (ports : I ↪ K)
    (base : Tapes K) (contents : Tapes I) (i : I) (word : List Bool) :
    fill ports base (Function.update contents i word) =
      Function.update (fill ports base contents) (ports i) word := by
  classical
  funext k
  by_cases hk : k = ports i
  · subst k
    simp only [fill_at, Function.update_self]
  · by_cases hr : ∃ j, ports j = k
    · rcases hr with ⟨j, rfl⟩
      have hj : j ≠ i := fun h => hk (congrArg ports h)
      rw [fill_at, Function.update_of_ne hj, Function.update_of_ne hk, fill_at]
    · rw [fill_other ports base _ k (not_exists.mp hr), Function.update_of_ne hk,
        fill_other ports base _ k (not_exists.mp hr)]

theorem fill_comp (ports : I ↪ K) (innerPorts : J ↪ I) (base : Tapes K)
    (outer : Tapes I) (inner : Tapes J) :
    fill (innerPorts.trans ports) (fill ports base outer) inner =
      fill ports base (fill innerPorts outer inner) := by
  classical
  funext k
  by_cases houter : ∃ i, ports i = k
  · rcases houter with ⟨i, rfl⟩
    rw [fill_at]
    by_cases hinner : ∃ j, innerPorts j = i
    · rcases hinner with ⟨j, rfl⟩
      have h := fill_at (innerPorts.trans ports) (fill ports base outer) inner j
      change fill (innerPorts.trans ports) (fill ports base outer) inner
        (ports (innerPorts j)) = inner j at h
      rw [h, fill_at]
    · have outside : ∀ j, (innerPorts.trans ports) j ≠ ports i := by
        intro j h
        exact hinner ⟨j, ports.injective h⟩
      rw [fill_other _ _ _ _ outside, fill_at,
        fill_other innerPorts outer inner i (not_exists.mp hinner)]
  · have outside : ∀ j, (innerPorts.trans ports) j ≠ k := by
      intro j h
      exact houter ⟨innerPorts j, h⟩
    rw [fill_other _ _ _ _ outside,
      fill_other ports base outer k (not_exists.mp houter),
      fill_other ports base _ k (not_exists.mp houter)]

def placedLabel (labels : L → Λ) (haltTarget : Option Λ) : Option L → Option Λ
  | none => haltTarget
  | some label => some (labels label)

noncomputable def configuration (ports : I ↪ K) (labels : L → Λ)
    (haltTarget : Option Λ) (base : Tapes K)
    (cfg : TM2.Cfg (fun _ : I => Bool) L σ) : TM2.Cfg (fun _ : K => Bool) Λ σ where
  l := placedLabel labels haltTarget cfg.l
  var := cfg.var
  stk := fill ports base cfg.stk

def statement (ports : I ↪ K) (labels : L → Λ) (haltTarget : Option Λ) :
    TM2.Stmt (fun _ : I => Bool) L σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | .push i value next => .push (ports i) value (statement ports labels haltTarget next)
  | .peek i observe next => .peek (ports i) observe (statement ports labels haltTarget next)
  | .pop i observe next => .pop (ports i) observe (statement ports labels haltTarget next)
  | .load update next => .load update (statement ports labels haltTarget next)
  | .branch predicate yes no => .branch predicate
      (statement ports labels haltTarget yes) (statement ports labels haltTarget no)
  | .goto next => .goto (fun state => labels (next state))
  | .halt => match haltTarget with
      | none => .halt
      | some label => .goto (fun _ => label)

variable [DecidableEq I] [DecidableEq K]

theorem stepAux_simulation (ports : I ↪ K) (labels : L → Λ) (haltTarget : Option Λ)
    (base : Tapes K) (q : TM2.Stmt (fun _ : I => Bool) L σ)
    (state : σ) (contents : Tapes I) :
    TM2.stepAux (statement ports labels haltTarget q) state (fill ports base contents) =
      configuration ports labels haltTarget base (TM2.stepAux q state contents) := by
  induction q generalizing state contents with
  | push i value next ih =>
      simp only [statement, TM2.stepAux, fill_at]
      rw [← fill_update]
      exact ih state (Function.update contents i (value state :: contents i))
  | peek i observe next ih =>
      simpa only [statement, TM2.stepAux, fill_at] using
        ih (observe state (contents i).head?) contents
  | pop i observe next ih =>
      simp only [statement, TM2.stepAux, fill_at]
      rw [← fill_update]
      exact ih (observe state (contents i).head?) (Function.update contents i (contents i).tail)
  | load update next ih =>
      simpa only [statement, TM2.stepAux] using ih (update state) contents
  | branch predicate yes no ihYes ihNo =>
      cases h : predicate state
      · simpa only [statement, TM2.stepAux, h, Bool.cond_false] using ihNo state contents
      · simpa only [statement, TM2.stepAux, h, Bool.cond_true] using ihYes state contents
  | goto next => rfl
  | halt => cases haltTarget <;> rfl

theorem step_simulation (ports : I ↪ K) (labels : L → Λ) (haltTarget : Option Λ)
    (base : Tapes K) (source : L → TM2.Stmt (fun _ : I => Bool) L σ)
    (ambientProgram : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (atLabels : ∀ l, ambientProgram (labels l) = statement ports labels haltTarget (source l))
    (a b : TM2.Cfg (fun _ : I => Bool) L σ)
    (transition : TM2.step source a = some b) :
    TM2.step ambientProgram (configuration ports labels haltTarget base a) =
      some (configuration ports labels haltTarget base b) := by
  cases a with
  | mk label state contents =>
      cases label with
      | none => simp [TM2.step] at transition
      | some label =>
          have result : TM2.stepAux (source label) state contents = b := Option.some.inj transition
          rw [← result]
          change some (TM2.stepAux (ambientProgram (labels label)) state
            (fill ports base contents)) = _
          rw [atLabels, stepAux_simulation]

theorem trace (ports : I ↪ K) (labels : L → Λ) (haltTarget : Option Λ)
    (base : Tapes K) (source : L → TM2.Stmt (fun _ : I => Bool) L σ)
    (ambientProgram : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (atLabels : ∀ l, ambientProgram (labels l) = statement ports labels haltTarget (source l))
    (steps : Nat) (start finish : TM2.Cfg (fun _ : I => Bool) L σ)
    (sourceTrace : (MachineComposition.advance (TM2.step source))^[steps] (some start) = some finish) :
    (MachineComposition.advance (TM2.step ambientProgram))^[steps]
      (some (configuration ports labels haltTarget base start)) =
        some (configuration ports labels haltTarget base finish) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step ambientProgram)
    (configuration ports labels haltTarget base)
    (step_simulation ports labels haltTarget base source ambientProgram atLabels)
    steps start finish sourceTrace

noncomputable def execution (ports : I ↪ K) (labels : L → Λ) (haltTarget : Option Λ)
    (base : Tapes K) (source : L → TM2.Stmt (fun _ : I => Bool) L σ)
    (ambientProgram : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (atLabels : ∀ l, ambientProgram (labels l) = statement ports labels haltTarget (source l))
    {start finish : TM2.Cfg (fun _ : I => Bool) L σ} {budget : Nat}
    (sourceRun : StateTransition.EvalsToInTime (TM2.step source) start (some finish) budget) :
    StateTransition.EvalsToInTime (TM2.step ambientProgram)
      (configuration ports labels haltTarget base start)
      (some (configuration ports labels haltTarget base finish)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step ambientProgram)
    (configuration ports labels haltTarget base)
    (step_simulation ports labels haltTarget base source ambientProgram atLabels) sourceRun

end BinPackingGames.Foundations.Complexity.CookLevin.ForestPlacement

namespace BinPackingGames.Foundations.Complexity.CookLevin.RootRefresh

open Turing MachineComposition
open BinPackingGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def guard (source : K) (start : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => start)
      (.load (fun state => (state.1, none))
        (Reduction.MachineTransfer.exitAt source exit)))

theorem guardStep_nil (source : K) (again start : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program again = guard source start exit)
    (base : K → List Bool) (hinput : base source = [])
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some again, (ambient, register), base⟩ =
      some ⟨exit, (ambient, none), base⟩ := by
  change some (TM2.stepAux (program again) (ambient, register) base) = _
  rw [atGuard]
  cases exit <;> simp [guard, TM2.stepAux, hinput, Reduction.MachineTransfer.exitAt]

theorem guardStep_nonempty (source : K) (again start : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program again = guard source start exit)
    (base : K → List Bool) (hinput : base source ≠ [])
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some again, (ambient, register), base⟩ =
      some ⟨some start, (ambient, (base source).head?), base⟩ := by
  change some (TM2.stepAux (program again) (ambient, register) base) = _
  rw [atGuard]
  cases hs : base source with
  | nil => exact False.elim (hinput hs)
  | cons bit rest => simp [guard, TM2.stepAux, hs]

theorem fieldTapes_overwrite (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output input' output' : List Bool) :
    SourceMachine.fieldTapes source destination
      (SourceMachine.fieldTapes source destination base input output) input' output' =
        SourceMachine.fieldTapes source destination base input' output' := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [SourceMachine.fieldTapes, hne]
  · by_cases hd : k = destination
    · subst k
      simp [SourceMachine.fieldTapes]
    · simp [SourceMachine.fieldTapes, hs, hd]

def steps (values : List Nat) : Nat := values.sum + 3 * values.length + 1

@[simp] theorem steps_nil : steps [] = 1 := rfl

theorem steps_cons (n : Nat) (values : List Nat) :
    steps (n :: values) = steps values + (n + 3) := by
  simp only [steps, List.sum_cons, List.length_cons]
  omega

theorem steps_le_length (values : List Nat) :
    steps values ≤ 3 * (encodeWords values).length + 1 := by
  rw [encodeWords_length]
  unfold steps
  omega

theorem refreshTrace (source destination : K) (hne : source ≠ destination)
    (again start loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program again = guard source start exit)
    (atStart : program start = SourceMachine.fieldStart destination loopLabel)
    (atLoop : program loopLabel =
      SourceMachine.fieldLoop source destination loopLabel (some again))
    (base : K → List Bool) (values : List Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values]
      (some ⟨some again, (ambient, register),
        SourceMachine.fieldTapes source destination base (encodeWords values) output⟩) =
      some ⟨exit, (ambient, none),
        SourceMachine.fieldTapes source destination base [] (encodeWords values.reverse ++ output)⟩ := by
  induction values generalizing output register with
  | nil =>
    simpa only [steps_nil, Function.iterate_one, advance_some, encodeWords,
      List.reverse_nil, List.nil_append] using
      guardStep_nil source again start exit program atGuard
        (SourceMachine.fieldTapes source destination base [] output)
        (SourceMachine.fieldTapes_source source destination hne base [] output) ambient register
  | cons n values ih =>
    let initial := SourceMachine.fieldTapes source destination base
      (encodeWords (n :: values)) output
    have hinput : initial source = encodeWord n ++ encodeWords values := by
      simp only [initial, SourceMachine.fieldTapes_source source destination hne, encodeWords]
    have hnonempty : initial source ≠ [] := by
      intro h
      have hl := congrArg List.length h
      rw [hinput, List.length_append, encodeWord_length] at hl
      simp only [List.length_nil] at hl
      omega
    have hfield := (SourceMachine.fieldInTime source destination hne start loopLabel
      (some again) program atStart atLoop initial n (encodeWords values) hinput ambient
      (initial source).head?).evals_in_steps
    change (advance (TM2.step program))^[n + 2]
      (some ⟨some start, (ambient, (initial source).head?), initial⟩) =
        some ⟨some again, (ambient, none),
          SourceMachine.fieldTapes source destination initial (encodeWords values)
            (encodeWord n ++ initial destination)⟩ at hfield
    have hround :
        (advance (TM2.step program))^[n + 3]
          (some ⟨some again, (ambient, register), initial⟩) =
          some ⟨some again, (ambient, none),
            SourceMachine.fieldTapes source destination base (encodeWords values)
              (encodeWord n ++ output)⟩ := by
      change (advance (TM2.step program))^[(n + 2) + 1] _ = _
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [guardStep_nonempty source again start exit program atGuard initial hnonempty]
      simpa only [initial, SourceMachine.fieldTapes_destination,
        fieldTapes_overwrite source destination hne] using hfield
    rw [steps_cons, Function.iterate_add_apply, hround, ih]
    simp only [List.reverse_cons, encodeWords_append, encodeWords,
      List.append_nil, List.append_assoc]

def refreshInTime (source destination : K) (hne : source ≠ destination)
    (again start loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program again = guard source start exit)
    (atStart : program start = SourceMachine.fieldStart destination loopLabel)
    (atLoop : program loopLabel =
      SourceMachine.fieldLoop source destination loopLabel (some again))
    (base : K → List Bool) (values : List Nat) (hinput : base source = encodeWords values)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), SourceMachine.fieldTapes source destination base []
        (encodeWords values.reverse ++ base destination)⟩)
      (3 * (encodeWords values).length + 1) where
  steps := steps values
  evals_in_steps := by
    have h := refreshTrace source destination hne again start loopLabel exit program
      atGuard atStart atLoop base values (base destination) ambient register
    rw [← hinput, SourceMachine.fieldTapes_self] at h
    exact h
  steps_le_m := steps_le_length values

theorem refresh_other (source destination other : K) (hs : other ≠ source)
    (hd : other ≠ destination) (base : K → List Bool) (values : List Nat) :
    SourceMachine.fieldTapes source destination base []
      (encodeWords values.reverse ++ base destination) other = base other :=
  SourceMachine.fieldTapes_other source destination other hs hd base _ _

inductive Label
  | guard | start | loop
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.guard, .start, .loop]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def program (source destination : K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .guard => guard source .start none
  | .start => SourceMachine.fieldStart destination .loop
  | .loop => SourceMachine.fieldLoop source destination .loop (some .guard)

abbrev machine : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := .guard
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program 0 1

theorem machineTrace (values : List Nat) :
    (advance machine.step)^[steps values]
      (some (initList machine (encodeWords values))) =
        some (haltList machine (encodeWords values.reverse)) := by
  let base : Fin 2 → List Bool := fun _ => []
  have h := refreshTrace (σ := Unit) 0 1 (by decide) .guard .start .loop none
    (program 0 1) rfl rfl rfl base values [] () none
  have hinit : SourceMachine.fieldTapes 0 1 base (encodeWords values) [] =
      (initList machine (encodeWords values)).stk := by
    funext k
    fin_cases k <;> simp [SourceMachine.fieldTapes, base, initList, machine]
  have hhalt : SourceMachine.fieldTapes 0 1 base [] (encodeWords values.reverse ++ []) =
      (haltList machine (encodeWords values.reverse)).stk := by
    funext k
    fin_cases k <;> simp [SourceMachine.fieldTapes, base, haltList, machine]
  rw [hinit, hhalt] at h
  exact h

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeWords encodeWords (List.reverse : List Nat → List Nat) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X + 1
  outputsFun values := {
    steps := steps values
    evals_in_steps := by
      change (advance machine.step)^[steps values]
        (some (initList machine ((encodeWords values).map id))) =
          some (haltList machine ((encodeWords values.reverse).map id))
      simp only [List.map_id_fun]
      exact machineTrace values
    steps_le_m := by simpa using steps_le_length values }

end BinPackingGames.Foundations.Complexity.CookLevin.RootRefresh

namespace BinPackingGames.Foundations.Complexity.CookLevin.ForestStage

open Turing MachineComposition StatementCircuit CircuitBatch CircuitProducerModel
open PostfixModel PostfixAlignment

inductive Tape
  | lower (tape : PostfixMachine.Tape)
  | tokens | records | rootTable
  deriving DecidableEq, Fintype

abbrev Ports (K : Type) := Tape ↪ K
abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

inductive Label
  | reverseTokens
  | lower (label : PostfixMachine.Label)
  | reverseRecords | drainRoots | rootGuard | rootStart | rootLoop | finish
  deriving DecidableEq, Fintype

def lowerPorts {K : Type} (ports : Ports K) : PostfixMachine.Tape ↪ K :=
  ⟨fun t => ports (.lower t), by
    intro a b h
    exact Tape.lower.inj (ports.injective h)⟩

def initialLocal (start : Nat) (tokens : List Token)
    (oldRecords oldRoots : List Bool) : Tape → List Bool
  | .lower .current => encodeWord start
  | .lower .remaining => encodeWord tokens.length
  | .tokens => (tokenBits tokens).reverse
  | .records => oldRecords
  | .rootTable => oldRoots
  | _ => []

def finalLocal (next : Nat) (roots : List Nat)
    (newRecords oldRecords : List Bool) : Tape → List Bool
  | .lower .current => encodeWord next
  | .lower .remaining => encodeWord 0
  | .records => newRecords.reverse ++ oldRecords
  | .rootTable => encodeWords roots.reverse
  | _ => []

def coreBase (tokens : List Token) : PostfixMachine.Tape → List Bool
  | .remaining => encodeWord tokens.length
  | _ => []

def coreInitial (start : Nat) (tokens : List Token) : PostfixMachine.Tape → List Bool :=
  PostfixMachine.boundaryTapes (coreBase tokens) start [] (tokenBits tokens)

def coreFinal (next : Nat) (roots : List Nat) (records : List Bool) :
    PostfixMachine.Tape → List Bool :=
  PostfixMachine.finalTapes (fun _ => []) next roots [] records

private theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

theorem coreTrace (tokens : List Token) (start next : Nat) (roots : List Nat)
    (gates : List Gate)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step PostfixMachine.program))^[
      PostfixMachine.tokensSteps start [] tokens +
        (recordsBits (gateRecords start gates)).length + 3]
      (some ⟨some .guard, PostfixMachine.initialState, coreInitial start tokens⟩) =
      some ⟨none, PostfixMachine.initialState,
        coreFinal next roots (recordsBits (gateRecords start gates))⟩ := by
  let bits := recordsBits (gateRecords start gates)
  let middle := PostfixMachine.boundaryTapes
    (PostfixMachine.outputTapes
      (Function.update (coreBase tokens) .remaining (encodeWord 0)) bits.reverse)
    next roots []
  have first := PostfixMachine.tokensTrace tokens (coreBase tokens) start [] next roots
    gates [] valid (by rfl)
  simp only [List.append_nil] at first
  have second := PostfixMachine.reverseTrace middle bits
    (by simp [middle, PostfixMachine.boundaryTapes, PostfixMachine.outputTapes])
    (by simp [middle, PostfixMachine.boundaryTapes, PostfixMachine.outputTapes, coreBase])
  have result := chain first second
  have frame : PostfixMachine.reversedTapes middle bits = coreFinal next roots bits := by
    funext tape
    cases tape <;> simp [PostfixMachine.reversedTapes, middle, coreFinal,
      PostfixMachine.finalTapes, PostfixMachine.boundaryTapes, PostfixMachine.outputTapes,
      coreBase]
  rw [frame] at result
  simpa only [coreInitial, bits, Nat.add_assoc] using result

def stateEquiv (σ : Type) : PostfixMachine.State × (σ × Bool) ≃ State σ where
  toFun state := (state.2, state.1.2)
  invFun state := (((), state.2), state.1)
  left_inv state := by rcases state with ⟨⟨u, register⟩, ambient⟩; cases u; rfl
  right_inv _ := rfl

def framedStatement {σ : Type}
    (stmt : TM2.Stmt PostfixMachine.Alphabet PostfixMachine.Label PostfixMachine.State) :
    TM2.Stmt PostfixMachine.Alphabet PostfixMachine.Label (State σ) :=
  MachineControl.statement id (stateEquiv σ) (MachineStateFrame.frameStatement stmt)

def framedProgram {σ : Type} :
    PostfixMachine.Label → TM2.Stmt PostfixMachine.Alphabet PostfixMachine.Label (State σ) :=
  fun label => framedStatement (PostfixMachine.program label)

def framedCfg {σ : Type} (ambient : σ × Bool) (cfg : PostfixMachine.machine.Cfg) :
    TM2.Cfg PostfixMachine.Alphabet PostfixMachine.Label (State σ) :=
  MachineControl.configuration id (stateEquiv σ)
    (MachineStateFrame.frameConfiguration ambient cfg)

theorem framed_step {σ : Type} (ambient : σ × Bool)
    (a b : PostfixMachine.machine.Cfg) (h : PostfixMachine.machine.step a = some b) :
    TM2.step framedProgram (framedCfg ambient a) = some (framedCfg ambient b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at h
    | some label =>
      have hb : TM2.stepAux (PostfixMachine.program label) state tapes = b := Option.some.inj h
      rw [← hb]
      change some (TM2.stepAux
        (MachineControl.statement id (stateEquiv σ)
          (MachineStateFrame.frameStatement (PostfixMachine.program label)))
        (stateEquiv σ (state, ambient)) tapes) = _
      erw [MachineControl.stepAux_simulation, MachineStateFrame.frame_stepAux]
      rfl

theorem framed_coreTrace {σ : Type} (ambient : σ × Bool)
    (tokens : List Token) (start next : Nat) (roots : List Nat) (gates : List Gate)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step framedProgram))^[PostfixMachine.tokensSteps start [] tokens +
        (recordsBits (gateRecords start gates)).length + 3]
      (some ⟨some .guard, (ambient, none), coreInitial start tokens⟩) =
      some ⟨none, (ambient, none), coreFinal next roots (recordsBits (gateRecords start gates))⟩ :=
  liftSuccessfulTrace PostfixMachine.machine.step (TM2.step framedProgram)
    (framedCfg ambient) (framed_step ambient) _ _ _ (coreTrace tokens start next roots gates valid)

def steps (tokens : List Token) (start : Nat) (roots : List Nat) (gates : List Gate)
    (oldRoots : List Bool) : Nat :=
  (tokenBits tokens).length + PostfixMachine.tokensSteps start [] tokens +
    2 * (recordsBits (gateRecords start gates)).length + oldRoots.length +
    RootRefresh.steps roots + 7

private theorem forest_length_le_cost {ι : Type*} (es : List (Expr ι)) :
    es.length ≤ Batch.cost es := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have hp := e.size_pos
    simp only [List.length_cons, Batch.cost_cons]
    omega

private theorem forest_rootsBits_length_le {ι : Type*}
    (es : List (Expr ι)) (start : Nat) :
    (encodeWords (Batch.roots start es).reverse).length ≤
      Batch.cost es * (start + Batch.cost es + 1) := by
  have h := encodeWords_length_le (Batch.roots start es).reverse
    (start + Batch.cost es) (by
      intro r hr
      exact (Batch.roots_bounds start es r (List.mem_reverse.mp hr)).2.le)
  have h' : (encodeWords (Batch.roots start es).reverse).length ≤
      es.length * (start + Batch.cost es + 1) := by
    simpa only [List.length_reverse, Batch.roots_length] using h
  exact h'.trans (Nat.mul_le_mul_right _ (forest_length_le_cost es))

private theorem forest_rootRefresh_le {ι : Type*} (es : List (Expr ι)) (start : Nat) :
    RootRefresh.steps (Batch.roots start es).reverse ≤
      3 * (Batch.cost es * (start + Batch.cost es + 1)) + 1 :=
  (RootRefresh.steps_le_length _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (forest_rootsBits_length_le es start)) 1)

private theorem forest_cost_quadratic (start c T R S G H : Nat)
    (hS : S ≤ c * (12 * (start + c) + 25))
    (hG : G ≤ 4 * c * (start + c + 5))
    (hH : H ≤ 3 * (c * (start + c + 1)) + 1) :
    let m := start + c + T + R + 1
    T + S + 2 * G + R + H + 7 ≤ 25 * m ^ 2 + 80 * m + 20 := by
  dsimp only
  let m := start + c + T + R + 1
  change T + S + 2 * G + R + H + 7 ≤ 25 * m ^ 2 + 80 * m + 20
  have hc : c ≤ m := by dsimp only [m]; omega
  have hsc : start + c ≤ m := by dsimp only [m]; omega
  have hsc1 : start + c + 1 ≤ m := by dsimp only [m]; omega
  have hTR : T + R ≤ m := by dsimp only [m]; omega
  have hS' : S ≤ m * (12 * m + 25) := hS.trans (Nat.mul_le_mul hc (by omega))
  have hG' : G ≤ 4 * m * (m + 5) :=
    hG.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hc) (by omega))
  have hr : c * (start + c + 1) ≤ m * m := Nat.mul_le_mul hc hsc1
  have hH' : H ≤ 3 * (m * m) + 1 :=
    hH.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hr) 1)
  calc
    _ ≤ (T + R) + m * (12 * m + 25) +
        2 * (4 * m * (m + 5)) + (3 * (m * m) + 1) + 7 := by omega
    _ ≤ m + m * (12 * m + 25) +
        2 * (4 * m * (m + 5)) + (3 * (m * m) + 1) + 7 := by omega
    _ = 23 * m ^ 2 + 66 * m + 8 := by ring
    _ ≤ 25 * m ^ 2 + 80 * m + 20 := by omega

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 25 * Polynomial.X ^ 2 + Polynomial.C 80 * Polynomial.X + Polynomial.C 20

theorem forest_steps_le {ι : Type*} (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (oldRoots : List Bool) (hw : ∀ i, wire i < start) :
    steps (forestTokens wire es) start (Batch.roots start es).reverse
        (Batch.gates wire start es) oldRoots ≤
      timePolynomial.eval (start + Batch.cost es + (tokenBits (forestTokens wire es)).length +
        oldRoots.length + 1) := by
  simp only [steps, timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  exact forest_cost_quadratic start (Batch.cost es)
    (tokenBits (forestTokens wire es)).length oldRoots.length
    (PostfixMachine.tokensSteps start [] (forestTokens wire es))
    (recordsBits (gateRecords start (Batch.gates wire start es))).length
    (RootRefresh.steps (Batch.roots start es).reverse)
    (PostfixBounds.forest_tokensSteps_le wire es start [] hw (by intro r hr; simp at hr))
    (PostfixBounds.forest_recordsBits_length_le wire es start hw)
    (forest_rootRefresh_le es start)

def localLowerPorts : PostfixMachine.Tape ↪ Tape :=
  ⟨Tape.lower, by intro a b h; exact Tape.lower.inj h⟩

def lowerFill (base : Tape → List Bool) (inner : PostfixMachine.Tape → List Bool) :
    Tape → List Bool
  | .lower tape => inner tape
  | tape => base tape

theorem fill_lower_eq (base : Tape → List Bool) (inner : PostfixMachine.Tape → List Bool) :
    ForestPlacement.fill localLowerPorts base inner = lowerFill base inner := by
  funext tape
  cases tape with
  | lower tape => exact ForestPlacement.fill_at localLowerPorts base inner tape
  | tokens => exact ForestPlacement.fill_other _ _ _ _ (by intro i; simp [localLowerPorts])
  | records => exact ForestPlacement.fill_other _ _ _ _ (by intro i; simp [localLowerPorts])
  | rootTable => exact ForestPlacement.fill_other _ _ _ _ (by intro i; simp [localLowerPorts])

def program {σ : Type} : Label → TM2.Stmt (Alphabet (K := Tape)) Label (State σ)
  | .reverseTokens => Reduction.MachineTransfer.loopAt .tokens (.lower .input) id false
      .reverseTokens (some (.lower .guard))
  | .lower label => ForestPlacement.statement localLowerPorts Label.lower
      (some .reverseRecords) (framedProgram label)
  | .reverseRecords => Reduction.MachineTransfer.loopAt (.lower .output) .records id false
      .reverseRecords (some .drainRoots)
  | .drainRoots => MachineDrain.drain .rootTable .drainRoots (some .rootGuard)
  | .rootGuard => RootRefresh.guard (.lower .roots) .rootStart (some .finish)
  | .rootStart => Hastad.SourceMachine.fieldStart .rootTable .rootLoop
  | .rootLoop => Hastad.SourceMachine.fieldLoop (.lower .roots) .rootTable .rootLoop
      (some .rootGuard)
  | .finish => .push (.lower .remaining) (fun _ => false)
      (.load (fun state => (state.1, none)) .halt)

def extras (oldRecords oldRoots : List Bool) : Tape → List Bool
  | .records => oldRecords
  | .rootTable => oldRoots
  | _ => []

def afterRecords (next : Nat) (roots : List Nat) (records oldRoots : List Bool) :
    Tape → List Bool
  | .lower .current => encodeWord next
  | .lower .roots => encodeWords roots
  | .records => records
  | .rootTable => oldRoots
  | _ => []

theorem localTrace {σ : Type} (ambient : σ × Bool)
    (tokens : List Token) (start next : Nat) (roots : List Nat) (gates : List Gate)
    (oldRecords oldRoots : List Bool)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step program))^[steps tokens start roots gates oldRoots]
      (some ⟨some .reverseTokens, (ambient, none), initialLocal start tokens oldRecords oldRoots⟩) =
      some ⟨none, (ambient, none),
        finalLocal next roots (recordsBits (gateRecords start gates)) oldRecords⟩ := by
  let bits := recordsBits (gateRecords start gates)
  let initial := initialLocal start tokens oldRecords oldRoots
  let ready := lowerFill (extras oldRecords oldRoots) (coreInitial start tokens)
  let compiled := lowerFill (extras oldRecords oldRoots) (coreFinal next roots bits)
  let merged := afterRecords next roots (bits.reverse ++ oldRecords) oldRoots
  let refreshed := afterRecords next roots (bits.reverse ++ oldRecords) []
  let unseeded := Function.update (finalLocal next roots bits oldRecords) (.lower .remaining) []
  have inputTransfer := (Reduction.MachineTransfer.transferAtInTime
    Tape.tokens (.lower .input) (by decide) id false .reverseTokens
    (some (.lower .guard)) program rfl initial ambient none).evals_in_steps
  have inputFrame : Reduction.MachineTransfer.tapesAt Tape.tokens (.lower .input) initial []
      ((initial .tokens).reverse.map id ++ initial (.lower .input)) = ready := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Reduction.MachineTransfer.tapesAt, initial,
        initialLocal, ready, lowerFill, coreInitial, PostfixMachine.boundaryTapes, coreBase, encodeWords]
    | tokens => simp [Reduction.MachineTransfer.tapesAt, initial, initialLocal, ready, lowerFill, extras]
    | records => simp [Reduction.MachineTransfer.tapesAt, initial, initialLocal, ready, lowerFill, extras]
    | rootTable => simp [Reduction.MachineTransfer.tapesAt, initial, initialLocal, ready, lowerFill, extras]
  change (advance (TM2.step program))^[(initial .tokens).length + 1]
    (some ⟨some .reverseTokens, (ambient, none), initial⟩) =
      some ⟨some (.lower .guard), (ambient, none), _⟩ at inputTransfer
  rw [inputFrame] at inputTransfer
  have hinputLength : (initial .tokens).length = (tokenBits tokens).length := by
    simp [initial, initialLocal]
  rw [hinputLength] at inputTransfer
  have lowering := ForestPlacement.trace localLowerPorts Label.lower (some .reverseRecords)
    (extras oldRecords oldRoots) framedProgram program (fun _ => rfl) _ _ _
    (framed_coreTrace ambient tokens start next roots gates valid)
  change (advance (TM2.step program))^[PostfixMachine.tokensSteps start [] tokens + bits.length + 3]
      (some ⟨some (.lower .guard), (ambient, none),
        ForestPlacement.fill localLowerPorts (extras oldRecords oldRoots) (coreInitial start tokens)⟩) =
      some ⟨some .reverseRecords, (ambient, none),
        ForestPlacement.fill localLowerPorts (extras oldRecords oldRoots) (coreFinal next roots bits)⟩ at lowering
  rw [fill_lower_eq, fill_lower_eq] at lowering
  have recordTransfer := (Reduction.MachineTransfer.transferAtInTime
    (Tape.lower .output) .records (by decide) id false .reverseRecords (some .drainRoots)
    program rfl compiled ambient none).evals_in_steps
  have recordFrame : Reduction.MachineTransfer.tapesAt (Tape.lower .output) .records compiled []
      ((compiled (.lower .output)).reverse.map id ++ compiled .records) = merged := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Reduction.MachineTransfer.tapesAt, compiled,
        lowerFill, extras, coreFinal, PostfixMachine.finalTapes, merged, afterRecords]
    | tokens => simp [Reduction.MachineTransfer.tapesAt, compiled, lowerFill, extras, merged, afterRecords]
    | records => simp [Reduction.MachineTransfer.tapesAt, compiled, lowerFill, extras,
        coreFinal, PostfixMachine.finalTapes, merged, afterRecords]
    | rootTable => simp [Reduction.MachineTransfer.tapesAt, compiled, lowerFill, extras, merged, afterRecords]
  change (advance (TM2.step program))^[(compiled (.lower .output)).length + 1]
    (some ⟨some .reverseRecords, (ambient, none), compiled⟩) =
      some ⟨some .drainRoots, (ambient, none), _⟩ at recordTransfer
  rw [recordFrame] at recordTransfer
  have hrecordLength : (compiled (.lower .output)).length = bits.length := by
    simp [compiled, lowerFill, coreFinal, PostfixMachine.finalTapes]
  rw [hrecordLength] at recordTransfer
  have draining := MachineDrain.drainTrace Tape.rootTable .drainRoots (some .rootGuard)
    program rfl merged (merged .rootTable) ambient none
  rw [Function.update_eq_self] at draining
  change (advance (TM2.step program))^[(merged .rootTable).length + 1]
    (some ⟨some .drainRoots, (ambient, none), merged⟩) =
      some ⟨some .rootGuard, (ambient, none), Function.update merged .rootTable []⟩ at draining
  have drainFrame : Function.update merged .rootTable [] = refreshed := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [merged, refreshed, afterRecords]
    | tokens => simp [merged, refreshed, afterRecords]
    | records => simp [merged, refreshed, afterRecords]
    | rootTable => simp [merged, refreshed, afterRecords]
  rw [drainFrame] at draining
  have hrootLength : (merged .rootTable).length = oldRoots.length := rfl
  rw [hrootLength] at draining
  have refresh := RootRefresh.refreshTrace (Tape.lower .roots) .rootTable (by decide)
    .rootGuard .rootStart .rootLoop (some .finish) program rfl rfl rfl
    refreshed roots [] ambient none
  have refreshInitial : Hastad.SourceMachine.fieldTapes (Tape.lower .roots) .rootTable
      refreshed (encodeWords roots) [] = refreshed := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
    | tokens => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
    | records => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
    | rootTable => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
  have refreshFinal : Hastad.SourceMachine.fieldTapes (Tape.lower .roots) .rootTable
      refreshed [] (encodeWords roots.reverse ++ []) = unseeded := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Hastad.SourceMachine.fieldTapes, refreshed,
        afterRecords, unseeded, finalLocal]
    | tokens => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords, unseeded, finalLocal]
    | records => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords, unseeded, finalLocal]
    | rootTable => simp [Hastad.SourceMachine.fieldTapes, refreshed, unseeded, finalLocal]
  rw [refreshInitial, refreshFinal] at refresh
  have finish : (advance (TM2.step program))^[1]
      (some ⟨some .finish, (ambient, none), unseeded⟩) =
      some ⟨none, (ambient, none), finalLocal next roots bits oldRecords⟩ := by
    change some (TM2.stepAux (program .finish) (ambient, none) unseeded) = _
    simp [program, TM2.stepAux, unseeded, finalLocal, encodeWord, Function.update_idem]
  have total := chain (chain (chain (chain (chain inputTransfer lowering) recordTransfer) draining) refresh) finish
  have cost : (((((tokenBits tokens).length + 1 +
      (PostfixMachine.tokensSteps start [] tokens + bits.length + 3)) +
      (bits.length + 1)) + (oldRoots.length + 1)) + RootRefresh.steps roots) + 1 =
      steps tokens start roots gates oldRoots := by dsimp only [steps, bits]; omega
  simpa only [cost, initial, bits] using total

section Caller

variable {K Λ σ : Type} [DecidableEq K]

def statement (ports : Ports K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  fun label => ForestPlacement.statement ports labels exit (program label)

theorem traceAt (ports : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, target (labels label) = statement ports labels exit label)
    (base : K → List Bool) (ambient : σ × Bool) (tokens : List Token)
    (start next : Nat) (roots : List Nat) (gates : List Gate) (oldRecords oldRoots : List Bool)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step target))^[steps tokens start roots gates oldRoots]
      (some ⟨some (labels .reverseTokens), (ambient, none),
        ForestPlacement.fill ports base (initialLocal start tokens oldRecords oldRoots)⟩) =
      some ⟨exit, (ambient, none), ForestPlacement.fill ports base
        (finalLocal next roots (recordsBits (gateRecords start gates)) oldRecords)⟩ :=
  ForestPlacement.trace ports labels exit base program target atLabels _ _ _
    (localTrace ambient tokens start next roots gates oldRecords oldRoots valid)

theorem forestTraceAt {ι : Type} (ports : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, target (labels label) = statement ports labels exit label)
    (base : K → List Bool) (ambient : σ × Bool) (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (oldRecords oldRoots : List Bool) :
    (advance (TM2.step target))^[steps (forestTokens wire es) start
        (Batch.roots start es).reverse (Batch.gates wire start es) oldRoots]
      (some ⟨some (labels .reverseTokens), (ambient, none), ForestPlacement.fill ports base
        (initialLocal start (forestTokens wire es) oldRecords oldRoots)⟩) =
      some ⟨exit, (ambient, none), ForestPlacement.fill ports base
        (finalLocal (start + Batch.cost es) (Batch.roots start es).reverse
          (recordsBits (gateRecords start (Batch.gates wire start es))) oldRecords)⟩ := by
  apply traceAt ports labels exit target atLabels base ambient _ _ _ _ _ _ _
  simpa only [List.append_nil] using compile_forestTokens wire es start []

noncomputable def forestInPolynomialTime {ι : Type}
    (ports : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, target (labels label) = statement ports labels exit label)
    (base : K → List Bool) (ambient : σ × Bool) (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (oldRecords oldRoots : List Bool) (hw : ∀ i, wire i < start) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .reverseTokens), (ambient, none), ForestPlacement.fill ports base
        (initialLocal start (forestTokens wire es) oldRecords oldRoots)⟩
      (some ⟨exit, (ambient, none), ForestPlacement.fill ports base
        (finalLocal (start + Batch.cost es) (Batch.roots start es).reverse
          (recordsBits (gateRecords start (Batch.gates wire start es))) oldRecords)⟩)
      (timePolynomial.eval (start + Batch.cost es +
        (tokenBits (forestTokens wire es)).length + oldRoots.length + 1)) where
  steps := steps (forestTokens wire es) start (Batch.roots start es).reverse
    (Batch.gates wire start es) oldRoots
  evals_in_steps := forestTraceAt ports labels exit target atLabels base ambient wire es
    start oldRecords oldRoots
  steps_le_m := forest_steps_le wire es start oldRoots hw

def preparedSize (ports : Ports K) (tapes : K → List Bool) : Nat :=
  (tapes (ports (.lower .current))).length +
    (tapes (ports (.lower .remaining))).length + (tapes (ports .tokens)).length +
    (tapes (ports .rootTable)).length

omit [DecidableEq K] in
theorem preparedSize_initial (ports : Ports K) (base : K → List Bool)
    (start : Nat) (tokens : List Token) (oldRecords oldRoots : List Bool) :
    preparedSize ports (ForestPlacement.fill ports base
      (initialLocal start tokens oldRecords oldRoots)) =
      start + tokens.length + (tokenBits tokens).length + oldRoots.length + 2 := by
  simp only [preparedSize, ForestPlacement.fill_at, initialLocal, encodeWord_length,
    List.length_reverse]
  omega

noncomputable def forestInPreparedTime {ι : Type}
    (ports : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, target (labels label) = statement ports labels exit label)
    (base : K → List Bool) (ambient : σ × Bool) (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (oldRecords oldRoots : List Bool) (hw : ∀ i, wire i < start) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .reverseTokens), (ambient, none), ForestPlacement.fill ports base
        (initialLocal start (forestTokens wire es) oldRecords oldRoots)⟩
      (some ⟨exit, (ambient, none), ForestPlacement.fill ports base
        (finalLocal (start + Batch.cost es) (Batch.roots start es).reverse
          (recordsBits (gateRecords start (Batch.gates wire start es))) oldRecords)⟩)
      (timePolynomial.eval (preparedSize ports (ForestPlacement.fill ports base
        (initialLocal start (forestTokens wire es) oldRecords oldRoots)))) := by
  let run := forestInPolynomialTime ports labels exit target atLabels base ambient wire es
    start oldRecords oldRoots hw
  have sizeBound : start + Batch.cost es + (tokenBits (forestTokens wire es)).length +
      oldRoots.length + 1 ≤ preparedSize ports (ForestPlacement.fill ports base
        (initialLocal start (forestTokens wire es) oldRecords oldRoots)) := by
    rw [preparedSize_initial, forestTokens_length]
    omega
  exact { toEvalsTo := run.toEvalsTo
          steps_le_m := run.steps_le_m.trans (natPolynomial_eval_mono timePolynomial sizeBound) }

omit [DecidableEq K] in
theorem final_other (ports : Ports K) (base : K → List Bool)
    (next : Nat) (roots : List Nat) (records oldRecords : List Bool)
    (k : K) (outside : ∀ t, ports t ≠ k) :
    ForestPlacement.fill ports base (finalLocal next roots records oldRecords) k = base k :=
  ForestPlacement.fill_other ports base _ k outside

@[simp] theorem final_counter (next : Nat) (roots : List Nat) (records oldRecords : List Bool) :
    finalLocal next roots records oldRecords (.lower .remaining) = encodeWord 0 := rfl

theorem final_lower_clean (next : Nat) (roots : List Nat) (records oldRecords : List Bool)
    (tape : PostfixMachine.Tape) (hc : tape ≠ .current) (hr : tape ≠ .remaining) :
    finalLocal next roots records oldRecords (.lower tape) = [] := by
  cases tape <;> simp_all [finalLocal]

@[simp] theorem final_forest_roots {ι : Type} (start : Nat) (es : List (Expr ι))
    (records oldRecords : List Bool) :
    finalLocal (start + Batch.cost es) (Batch.roots start es).reverse records oldRecords
      .rootTable = encodeWords (Batch.roots start es) := by
  simp [finalLocal]

end Caller

def machine {σ : Type} [Fintype σ] (ambient : σ × Bool) : FinTM2 where
  K := Tape
  k₀ := .tokens
  k₁ := .records
  Γ := Alphabet
  Λ := Label
  main := .reverseTokens
  σ := State σ
  initialState := (ambient, none)
  m := program

theorem machine_alphabet_finite {σ : Type} [Fintype σ] (ambient : σ × Bool) :
    ∀ k, Finite ((machine ambient).Γ k) := by
  intro k
  exact inferInstanceAs (Finite Bool)

end BinPackingGames.Foundations.Complexity.CookLevin.ForestStage

end OAI
