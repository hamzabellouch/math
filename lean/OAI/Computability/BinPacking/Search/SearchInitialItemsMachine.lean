import OAI.Computability.BinPacking.Arithmetic.BinaryOrderMachine
import OAI.Computability.BinPacking.Arithmetic.BinaryTallyMachine
import OAI.Computability.BinPacking.Search.SearchInitializeEncoding

namespace OAI

namespace BinPackingGap.ExtensionMachineRegisters

open Turing.TM2
open BinPackingGames.Foundations.Complexity

structure Lens (Big Small : Type) where
  get : Big → Small
  set : Big → Small → Big
  get_set : ∀ s v, get (set s v) = v
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s v w, set (set s v) w = set s w

namespace Lens

variable {Big Small Middle : Type}

def identity (State : Type) : Lens State State where
  get := id
  set := fun _ v => v
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def ofEquiv (e : Small ≃ Big) : Lens Big Small where
  get := e.symm
  set := fun _ v => e v
  get_set _ v := e.symm_apply_apply v
  set_get s := e.apply_symm_apply s
  set_set _ _ _ := rfl

def first (Left Right : Type) : Lens (Left × Right) Left where
  get := Prod.fst
  set := fun s v => (v, s.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def second (Left Right : Type) : Lens (Left × Right) Right where
  get := Prod.snd
  set := fun s v => (s.1, v)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def compose (outer : Lens Big Middle) (inner : Lens Middle Small) : Lens Big Small where
  get s := inner.get (outer.get s)
  set s v := outer.set s (inner.set (outer.get s) v)
  get_set s v := by rw [outer.get_set, inner.get_set]
  set_get s := by rw [inner.set_get, outer.set_get]
  set_set s v w := by rw [outer.get_set, inner.set_set, outer.set_set]

end Lens

variable {K Label Big Small : Type} {Γ : K → Type}

def statement (lens : Lens Big Small) : Stmt Γ Label Small → Stmt Γ Label Big
  | .push k f next => .push k (fun s => f (lens.get s)) (statement lens next)
  | .peek k f next => .peek k (fun s symbol => lens.set s (f (lens.get s) symbol))
      (statement lens next)
  | .pop k f next => .pop k (fun s symbol => lens.set s (f (lens.get s) symbol))
      (statement lens next)
  | .load f next => .load (fun s => lens.set s (f (lens.get s))) (statement lens next)
  | .branch f yes no => .branch (fun s => f (lens.get s))
      (statement lens yes) (statement lens no)
  | .goto f => .goto (fun s => f (lens.get s))
  | .halt => .halt

@[simp] theorem statement_identity (q : Stmt Γ Label Small) :
    statement (Lens.identity Small) q = q := by
  induction q <;> simp_all [statement, Lens.identity]

theorem statement_compose {Middle : Type} (outer : Lens Big Middle)
    (inner : Lens Middle Small) (q : Stmt Γ Label Small) :
    statement (Lens.compose outer inner) q = statement outer (statement inner q) := by
  induction q <;> simp_all [statement, Lens.compose]

@[simp] theorem statement_ofEquiv_symm (e : Small ≃ Big) (q : Stmt Γ Label Big) :
    statement (Lens.ofEquiv e) (statement (Lens.ofEquiv e.symm) q) = q := by
  induction q <;> simp_all [statement, Lens.ofEquiv]

def equivConfiguration (e : Small ≃ Big) (c : Cfg Γ Label Small) : Cfg Γ Label Big :=
  ⟨c.l, e c.var, c.stk⟩

def configuration (lens : Lens Big Small) (base : Big) (c : Cfg Γ Label Small) :
    Cfg Γ Label Big := ⟨c.l, lens.set base c.var, c.stk⟩

def project (lens : Lens Big Small) (c : Cfg Γ Label Big) : Cfg Γ Label Small :=
  ⟨c.l, lens.get c.var, c.stk⟩

@[simp] theorem configuration_ofEquiv (e : Small ≃ Big) (base : Big)
    (c : Cfg Γ Label Small) :
    configuration (Lens.ofEquiv e) base c = equivConfiguration e c := rfl

@[simp] theorem equivConfiguration_symm (e : Small ≃ Big) (c : Cfg Γ Label Big) :
    equivConfiguration e (equivConfiguration e.symm c) = c := by
  cases c
  simp [equivConfiguration]

@[simp] theorem project_configuration (lens : Lens Big Small) (base : Big)
    (c : Cfg Γ Label Small) : project lens (configuration lens base c) = c := by
  cases c
  simp [project, configuration, lens.get_set]

@[simp] theorem configuration_project (lens : Lens Big Small) (c : Cfg Γ Label Big) :
    configuration lens c.var (project lens c) = c := by
  cases c
  simp [project, configuration, lens.set_get]

variable [DecidableEq K]

theorem stepAux_transport (lens : Lens Big Small) (base : Big)
    (q : Stmt Γ Label Small) (state : Small) (tapes : ∀ k, List (Γ k)) :
    stepAux (statement lens q) (lens.set base state) tapes =
      configuration lens base (stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
      simp only [statement, stepAux, lens.get_set]
      exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [statement, stepAux, lens.get_set, lens.set_set] using
        ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simpa only [statement, stepAux, lens.get_set, lens.set_set] using
        ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [statement, stepAux, lens.get_set, lens.set_set] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases test : f state with
      | false =>
          simpa only [statement, stepAux, lens.get_set, test, Bool.cond_false] using
            ihNo state tapes
      | true =>
          simpa only [statement, stepAux, lens.get_set, test, Bool.cond_true] using
            ihYes state tapes
  | goto f => simp [statement, stepAux, lens.get_set, configuration]
  | halt => rfl

theorem stepAux_transport_project (lens : Lens Big Small)
    (q : Stmt Γ Label Small) (state : Big) (tapes : ∀ k, List (Γ k)) :
    stepAux (statement lens q) state tapes =
      configuration lens state (stepAux q (lens.get state) tapes) := by
  simpa only [lens.set_get] using
    stepAux_transport lens state q (lens.get state) tapes

def program (lens : Lens Big Small) (source : Label → Stmt Γ Label Small) :
    Label → Stmt Γ Label Big := fun label => statement lens (source label)

omit [DecidableEq K] in
@[simp] theorem program_identity (source : Label → Stmt Γ Label Small) :
    program (Lens.identity Small) source = source := by
  funext label
  exact statement_identity (source label)

omit [DecidableEq K] in
@[simp] theorem program_ofEquiv_symm (e : Small ≃ Big)
    (target : Label → Stmt Γ Label Big) :
    program (Lens.ofEquiv e) (program (Lens.ofEquiv e.symm) target) = target := by
  funext label
  exact statement_ofEquiv_symm e (target label)

theorem step_transport (lens : Lens Big Small) (base : Big)
    (source : Label → Stmt Γ Label Small) (c : Cfg Γ Label Small) :
    step (program lens source) (configuration lens base c) =
      (step source c).map (configuration lens base) := by
  cases c with
  | mk label state tapes =>
      cases label with
      | none => rfl
      | some label =>
          change some (stepAux (statement lens (source label)) (lens.set base state) tapes) = _
          rw [stepAux_transport]
          rfl

theorem advance_transport (lens : Lens Big Small) (base : Big)
    (source : Label → Stmt Γ Label Small) (c : Option (Cfg Γ Label Small)) :
    MachineComposition.advance (step (program lens source)) (c.map (configuration lens base)) =
      (MachineComposition.advance (step source) c).map (configuration lens base) := by
  cases c with
  | none => rfl
  | some c => exact step_transport lens base source c

theorem iterate_transport (lens : Lens Big Small) (base : Big)
    (source : Label → Stmt Γ Label Small) (steps : Nat) (c : Option (Cfg Γ Label Small)) :
    (MachineComposition.advance (step (program lens source)))^[steps]
        (c.map (configuration lens base)) =
      ((MachineComposition.advance (step source))^[steps] c).map (configuration lens base) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih, advance_transport,
        Function.iterate_succ_apply']

theorem trace (lens : Lens Big Small) (base : Big)
    (source : Label → Stmt Γ Label Small) (steps : Nat)
    (start finish : Cfg Γ Label Small)
    (run : (MachineComposition.advance (step source))^[steps] (some start) = some finish) :
    (MachineComposition.advance (step (program lens source)))^[steps]
      (some (configuration lens base start)) = some (configuration lens base finish) := by
  change (MachineComposition.advance (step (program lens source)))^[steps]
      ((some start).map (configuration lens base)) = (some finish).map (configuration lens base)
  rw [iterate_transport, run]

def execution (lens : Lens Big Small) (base : Big)
    (source : Label → Stmt Γ Label Small)
    {start : Cfg Γ Label Small} {finish : Option (Cfg Γ Label Small)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program lens source))
      (configuration lens base start) (finish.map (configuration lens base)) budget where
  steps := run.steps
  evals_in_steps := by
    have executed := run.evals_in_steps
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish at executed
    change (MachineComposition.advance (step (program lens source)))^[run.steps]
      ((some start).map (configuration lens base)) = finish.map (configuration lens base)
    rw [iterate_transport, executed]
  steps_le_m := run.steps_le_m

def equivExecution (e : Small ≃ Big) (target : Label → Stmt Γ Label Big)
    {start : Cfg Γ Label Small} {finish : Option (Cfg Γ Label Small)} {budget : Nat}
    (run : StateTransition.EvalsToInTime
      (step (program (Lens.ofEquiv e.symm) target)) start finish budget) :
    StateTransition.EvalsToInTime (step target) (equivConfiguration e start)
      (finish.map (equivConfiguration e)) budget := by
  have mapped : configuration (Γ := Γ) (Label := Label) (Lens.ofEquiv e) (e start.var) =
      equivConfiguration e := by
    funext c
    exact configuration_ofEquiv e _ c
  simpa only [program_ofEquiv_symm, mapped] using
    execution (Lens.ofEquiv e) (e start.var)
      (program (Lens.ofEquiv e.symm) target) run

theorem equivTrace (e : Small ≃ Big) (target : Label → Stmt Γ Label Big)
    (steps : Nat) (start finish : Cfg Γ Label Small)
    (run : (MachineComposition.advance
      (step (program (Lens.ofEquiv e.symm) target)))^[steps] (some start) = some finish) :
    (MachineComposition.advance (step target))^[steps]
      (some (equivConfiguration e start)) = some (equivConfiguration e finish) := by
  simpa only [program_ofEquiv_symm, configuration_ofEquiv] using
    trace (Lens.ofEquiv e) (e start.var) (program (Lens.ofEquiv e.symm) target)
      steps start finish run

omit [DecidableEq K] in
theorem observer_configuration {Observed : Type} (lens : Lens Big Small)
    (observe : Big → Observed) (preserved : ∀ s v, observe (lens.set s v) = observe s)
    (base : Big) (c : Cfg Γ Label Small) :
    observe (configuration lens base c).var = observe base := preserved base c.var

end BinPackingGap.ExtensionMachineRegisters

namespace BinPackingGap.ExtensionMachinePlacement

open Turing BinPackingGames.Foundations.Complexity
open ExtensionMachineRegisters (Lens)

variable {K K' Label Label' Small Big : Type}

def tapes (view : K' → Option K) (source : K → List Bool)
    (extra : K' → List Bool) : K' → List Bool :=
  fun j => match view j with
    | some k => source k
    | none => extra j

def label (labels : Label → Label') (exit : Option Label') : Option Label → Option Label'
  | some l => some (labels l)
  | none => exit

def configuration (view : K' → Option K) (labels : Label → Label')
    (exit : Option Label') (lens : Lens Big Small) (base : Big)
    (extra : K' → List Bool) (c : TM2.Cfg (fun _ : K => Bool) Label Small) :
    TM2.Cfg (fun _ : K' => Bool) Label' Big :=
  ⟨label labels exit c.l, lens.set base c.var, tapes view c.stk extra⟩

def statement (tape : K → K') (labels : Label → Label') (exit : Option Label')
    (lens : Lens Big Small) :
    TM2.Stmt (fun _ : K => Bool) Label Small → TM2.Stmt (fun _ : K' => Bool) Label' Big
  | .push k f next => .push (tape k) (fun s => f (lens.get s))
      (statement tape labels exit lens next)
  | .peek k f next => .peek (tape k) (fun s bit => lens.set s (f (lens.get s) bit))
      (statement tape labels exit lens next)
  | .pop k f next => .pop (tape k) (fun s bit => lens.set s (f (lens.get s) bit))
      (statement tape labels exit lens next)
  | .load f next => .load (fun s => lens.set s (f (lens.get s)))
      (statement tape labels exit lens next)
  | .branch f yes no => .branch (fun s => f (lens.get s))
      (statement tape labels exit lens yes) (statement tape labels exit lens no)
  | .goto f => .goto (fun s => labels (f (lens.get s)))
  | .halt => match exit with
    | some l => .goto (fun _ => l)
    | none => .halt

@[simp] theorem tapes_apply (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (source : K → List Bool) (extra : K' → List Bool) (k : K) :
    tapes view source extra (tape k) = source k := by
  simp only [tapes, left]

@[simp] theorem tapes_unmapped (view : K' → Option K)
    (source : K → List Bool) (extra : K' → List Bool) (j : K')
    (unmapped : view j = none) : tapes view source extra j = extra j := by
  simp only [tapes, unmapped]

theorem tapes_restrict (tape : K → K') (view : K' → Option K)
    (right : ∀ j k, view j = some k → tape k = j) (base : K' → List Bool) :
    tapes view (fun k => base (tape k)) base = base := by
  funext j
  cases found : view j with
  | none => simp [tapes, found]
  | some k => simp [tapes, found, right j k found]

variable [DecidableEq K] [DecidableEq K']

theorem tapes_update (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (source : K → List Bool) (extra : K' → List Bool) (k : K) (word : List Bool) :
    tapes view (Function.update source k word) extra =
      Function.update (tapes view source extra) (tape k) word := by
  funext j
  by_cases same : j = tape k
  · subst j
    simp [tapes, left]
  · cases found : view j with
    | none => simp [tapes, found, same]
    | some i =>
      have distinct : i ≠ k := by
        intro equal
        subst i
        exact same (right j k found).symm
      simp [tapes, found, same, distinct]

theorem stepAux_simulation (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label → Label') (exit : Option Label') (lens : Lens Big Small)
    (base : Big) (extra : K' → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) Label Small)
    (state : Small) (source : K → List Bool) :
    TM2.stepAux (statement tape labels exit lens q) (lens.set base state)
        (tapes view source extra) =
      configuration view labels exit lens base extra (TM2.stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
      simp only [statement, TM2.stepAux, lens.get_set, tapes_apply tape view left]
      rw [← tapes_update tape view left right]
      exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
      simpa only [statement, TM2.stepAux, lens.get_set, lens.set_set,
        tapes_apply tape view left] using ih (f state (source k).head?) source
  | pop k f next ih =>
      simp only [statement, TM2.stepAux, lens.get_set, lens.set_set,
        tapes_apply tape view left]
      rw [← tapes_update tape view left right]
      exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih =>
      simpa only [statement, TM2.stepAux, lens.get_set, lens.set_set] using ih (f state) source
  | branch f yes no ihYes ihNo =>
      cases test : f state with
      | false =>
          simpa only [statement, TM2.stepAux, lens.get_set, test, Bool.cond_false] using
            ihNo state source
      | true =>
          simpa only [statement, TM2.stepAux, lens.get_set, test, Bool.cond_true] using
            ihYes state source
  | goto f => simp [statement, TM2.stepAux, lens.get_set, configuration, label]
  | halt => cases exit <;> rfl

theorem step_simulation (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label → Label') (exit : Option Label') (lens : Lens Big Small)
    (base : Big) (extra : K' → List Bool)
    (source : Label → TM2.Stmt (fun _ : K => Bool) Label Small)
    (target : Label' → TM2.Stmt (fun _ : K' => Bool) Label' Big)
    (atLabels : ∀ l, target (labels l) = statement tape labels exit lens (source l))
    (a b : TM2.Cfg (fun _ : K => Bool) Label Small)
    (run : TM2.step source a = some b) :
    TM2.step target (configuration view labels exit lens base extra a) =
      some (configuration view labels exit lens base extra b) := by
  cases a with
  | mk current state sourceTapes =>
      cases current with
      | none => simp [TM2.step] at run
      | some current =>
          have finish : TM2.stepAux (source current) state sourceTapes = b :=
            Option.some.inj run
          rw [← finish]
          change some (TM2.stepAux (target (labels current)) (lens.set base state)
            (tapes view sourceTapes extra)) = _
          rw [atLabels, stepAux_simulation tape view left right]

theorem trace (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label → Label') (exit : Option Label') (lens : Lens Big Small)
    (base : Big) (extra : K' → List Bool)
    (source : Label → TM2.Stmt (fun _ : K => Bool) Label Small)
    (target : Label' → TM2.Stmt (fun _ : K' => Bool) Label' Big)
    (atLabels : ∀ l, target (labels l) = statement tape labels exit lens (source l))
    (n : Nat) (a b : TM2.Cfg (fun _ : K => Bool) Label Small)
    (run : (MachineComposition.advance (TM2.step source))^[n] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[n]
      (some (configuration view labels exit lens base extra a)) =
      some (configuration view labels exit lens base extra b) :=
  MachineComposition.liftSuccessfulTrace _ _ _
    (step_simulation tape view left right labels exit lens base extra source target atLabels)
    n a b run

def execution (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label → Label') (exit : Option Label') (lens : Lens Big Small)
    (base : Big) (extra : K' → List Bool)
    (source : Label → TM2.Stmt (fun _ : K => Bool) Label Small)
    (target : Label' → TM2.Stmt (fun _ : K' => Bool) Label' Big)
    (atLabels : ∀ l, target (labels l) = statement tape labels exit lens (source l))
    {start finish : TM2.Cfg (fun _ : K => Bool) Label Small} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) start (some finish) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration view labels exit lens base extra start)
      (some (configuration view labels exit lens base extra finish)) budget :=
  MachineComposition.liftExecutionInTime _ _ _
    (step_simulation tape view left right labels exit lens base extra source target atLabels) run

omit [DecidableEq K] [DecidableEq K'] in
theorem configuration_observer {Observed : Type} (lens : Lens Big Small)
    (observe : Big → Observed) (preserved : ∀ s v, observe (lens.set s v) = observe s)
    (view : K' → Option K) (labels : Label → Label') (exit : Option Label')
    (base : Big) (extra : K' → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) Label Small) :
    observe (configuration view labels exit lens base extra c).var = observe base :=
  preserved base c.var

end BinPackingGap.ExtensionMachinePlacement

namespace BinPackingGap.ExtensionNatMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer

abbrev State (A : Type) := BinaryAddMachine.State A
abbrev Alphabet {K : Type} (_ : K) := Bool

inductive Label
  | scan | restore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .restore]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def scannerEquiv (A : Type) : BinPackingCompleteness.BinaryNameMachine.State (A × Bool) ≃ State A where
  toFun s := ((s.1, s.2.1), s.2.2)
  invFun s := (s.1.1, s.1.2, s.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable {K Λ A : Type} [DecidableEq K]

def statement (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (accepted rejected : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .scan =>
      ExtensionMachineRegisters.statement
        (ExtensionMachineRegisters.Lens.ofEquiv (scannerEquiv A))
        (BinPackingCompleteness.BinaryNameMachine.scan (slots 0) (slots 2)
          (labels .scan) (some (labels .restore)) rejected)
  | .restore => loopAt (slots 2) (slots 1) id false (labels .restore) accepted

def resultTapes (slots : Fin 3 ↪ K) (base : K → List Bool) (n : Nat)
    (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (slots 0) suffix) (slots 1) (n.bits ++ base (slots 1))

theorem natTrace (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (accepted rejected : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = statement slots labels accepted rejected label)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (input : base (slots 0) = BinaryEncoding.natBits n ++ suffix)
    (scratchEmpty : base (slots 2) = []) (ambient : A) :
    (MachineComposition.advance (TM2.step p))^[2 * n.size + 2]
      (some ⟨some (labels .scan), BinaryAddMachine.clean ambient, base⟩) =
      some ⟨accepted, BinaryAddMachine.clean ambient, resultTapes slots base n suffix⟩ := by
  let source := ExtensionMachineRegisters.program
    (ExtensionMachineRegisters.Lens.ofEquiv (scannerEquiv A).symm) p
  have atScan : source (labels .scan) =
      BinPackingCompleteness.BinaryNameMachine.scan (slots 0) (slots 2)
        (labels .scan) (some (labels .restore)) rejected := by
    change ExtensionMachineRegisters.statement
      (ExtensionMachineRegisters.Lens.ofEquiv (scannerEquiv A).symm) (p (labels .scan)) = _
    rw [atLabels .scan]
    exact ExtensionMachineRegisters.statement_ofEquiv_symm (scannerEquiv A).symm _
  have hd (i j : Fin 3) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
  have first := BinPackingCompleteness.BinaryNameMachine.framedTrace
    (slots 0) (slots 2) (hd 0 2 (by decide)) (labels .scan)
    (some (labels .restore)) rejected source atScan base (ambient, false)
    n.bits suffix [] none
  have canonical := BinPackingCompleteness.BinaryParsing.canonical_nat_bits n
  rw [canonical] at first
  simp only [↓reduceIte, List.append_nil] at first
  have translated := ExtensionMachineRegisters.equivTrace (scannerEquiv A) p _ _ _ first
  let afterScan := tapesAt (slots 0) (slots 2) base suffix n.bits.reverse
  have initial : tapesAt (slots 0) (slots 2) base
      (BinPackingCompleteness.BinaryNameMachine.frame n.bits ++ suffix) [] = base := by
    rw [BinPackingCompleteness.BinaryParsing.frame_eq]
    change tapesAt (slots 0) (slots 2) base (BinaryEncoding.natBits n ++ suffix) [] = base
    rw [← input, ← scratchEmpty]
    exact tapesAt_self _ _ _
  have translated' : (MachineComposition.advance (TM2.step p))^[n.size + 1]
      (some ⟨some (labels .scan), BinaryAddMachine.clean ambient, base⟩) =
      some ⟨some (labels .restore), BinaryAddMachine.clean ambient, afterScan⟩ := by
    simpa only [ExtensionMachineRegisters.equivConfiguration, scannerEquiv,
      Equiv.coe_fn_mk, BinPackingCompleteness.BinaryNameMachine.clean,
      BinaryAddMachine.clean, BinaryAddMachine.state, initial, afterScan,
      ← Nat.size_eq_bits_len] using translated
  have saved : afterScan (slots 2) = n.bits.reverse := by simp [afterScan, tapesAt]
  have destination : afterScan (slots 1) = base (slots 1) := by
    simp [afterScan, tapesAt, hd 1 0 (by decide), hd 1 2 (by decide)]
  have second := transferAt_fromTapes (slots 2) (slots 1) (hd 2 1 (by decide))
    (id : Bool → Bool) false (labels .restore) accepted p
    (by simpa only [statement] using atLabels .restore) afterScan
    ((ambient, false), none) none
  rw [saved, destination] at second
  have final : tapesAt (slots 2) (slots 1) afterScan []
      (n.bits ++ base (slots 1)) = resultTapes slots base n suffix := by
    funext k
    by_cases hout : k = slots 1
    · subst k; simp [tapesAt, resultTapes]
    by_cases hscratch : k = slots 2
    · subst k
      simp [tapesAt, resultTapes, hd 2 1 (by decide), hd 2 0 (by decide), scratchEmpty]
    simp [tapesAt, afterScan, resultTapes, hout, hscratch]
  have second' : (MachineComposition.advance (TM2.step p))^[n.size + 1]
      (some ⟨some (labels .restore), BinaryAddMachine.clean ambient, afterScan⟩) =
      some ⟨accepted, BinaryAddMachine.clean ambient, resultTapes slots base n suffix⟩ := by
    change (nextAt (Γ := Alphabet) (slots 1) p)^[n.size + 1]
      (some ⟨some (labels .restore), BinaryAddMachine.clean ambient, afterScan⟩) =
      some ⟨accepted, BinaryAddMachine.clean ambient, resultTapes slots base n suffix⟩
    simpa only [List.length_reverse, List.reverse_reverse, List.map_id_fun,
      id_eq, ← Nat.size_eq_bits_len, final, BinaryAddMachine.clean,
      BinaryAddMachine.state] using second
  rw [show 2 * n.size + 2 = (n.size + 1) + (n.size + 1) by omega,
    Function.iterate_add_apply, translated', second']

def natInTime (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (accepted rejected : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = statement slots labels accepted rejected label)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (input : base (slots 0) = BinaryEncoding.natBits n ++ suffix)
    (scratchEmpty : base (slots 2) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .scan), BinaryAddMachine.clean ambient, base⟩
      (some ⟨accepted, BinaryAddMachine.clean ambient, resultTapes slots base n suffix⟩)
      (2 * n.size + 2) where
  steps := 2 * n.size + 2
  evals_in_steps := natTrace slots labels accepted rejected p atLabels base n suffix
    input scratchEmpty ambient
  steps_le_m := Nat.le_refl _

def orderEquiv (A : Type) : BinaryOrderMachine.State (A × Bool) ≃ State (A × Ordering) where
  toFun
    | ((((ambient, carry), order), left), right) => ((((ambient, order), carry), left), right)
  invFun
    | ((((ambient, order), carry), left), right) => ((((ambient, carry), order), left), right)
  left_inv _ := rfl
  right_inv _ := rfl

def orderStatement (slots : Fin 5 ↪ K) (labels : BinaryOrderMachine.PreserveLabel → Λ)
    (exits : Ordering → Option Λ) (label : BinaryOrderMachine.PreserveLabel) :
    TM2.Stmt (Alphabet (K := K)) Λ (State (A × Ordering)) :=
  ExtensionMachineRegisters.statement
    (ExtensionMachineRegisters.Lens.ofEquiv (orderEquiv A))
    (BinaryOrderMachine.preservingInstruction slots labels exits label)

def preservingOrderInTime (slots : Fin 5 ↪ K)
    (labels : BinaryOrderMachine.PreserveLabel → Λ) (exits : Ordering → Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State (A × Ordering)))
    (atLabels : ∀ label, p (labels label) = orderStatement slots labels exits label)
    (base : K → List Bool) (a b : Nat)
    (leftWord : base (slots 0) = a.bits) (rightWord : base (slots 1) = b.bits)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (scratchEmpty : base (slots 4) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .leftOut), BinaryAddMachine.clean (ambient, .eq), base⟩
      (some ⟨exits (BinaryOrderMachine.orderNat a b .eq),
        BinaryAddMachine.clean (ambient, .eq), base⟩)
      (BinaryOrderMachine.preservingSteps a.size b.size) := by
  let source := ExtensionMachineRegisters.program
    (ExtensionMachineRegisters.Lens.ofEquiv (orderEquiv A).symm) p
  have atSource : ∀ label, source (labels label) =
      BinaryOrderMachine.preservingInstruction slots labels exits label := by
    intro label
    change ExtensionMachineRegisters.statement
      (ExtensionMachineRegisters.Lens.ofEquiv (orderEquiv A).symm) (p (labels label)) = _
    rw [atLabels]
    exact ExtensionMachineRegisters.statement_ofEquiv_symm (orderEquiv A).symm _
  have run := BinaryOrderMachine.preservingNatInTime slots labels exits source atSource
    base a b leftWord rightWord leftEmpty rightEmpty scratchEmpty (ambient, false)
  have lifted := ExtensionMachineRegisters.equivExecution (orderEquiv A) p run
  simpa only [ExtensionMachineRegisters.equivConfiguration, orderEquiv,
    Equiv.coe_fn_mk, BinaryOrderMachine.clean, BinaryAddMachine.clean,
    BinaryAddMachine.state, Option.map_some] using lifted

end BinPackingGap.ExtensionNatMachine

namespace BinPackingGap.SearchInitialItemsMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open SearchInitializeEncoding
open BinPackingGames.Reduction.MachineTransfer

inductive Number
  | numerator | denominator
  deriving DecidableEq

protected abbrev Number.enumList : List Number := [.numerator, .denominator]

protected theorem Number.enumList_getElem?_ctorIdx_eq (x : Number) :
    Number.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Number.enumList_nodup : Number.enumList.Nodup := by decide

instance : Fintype Number where
  elems := ⟨Number.enumList, Number.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Control
  | entry | malformedDrain | malformedFinish | copyOut | copyBack | seed
  | marker | positive | failed | clearNumerator | clearDenominator
  | countOut | countBack | finish
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.entry, .malformedDrain, .malformedFinish,
  .copyOut, .copyBack, .seed, .marker, .positive, .failed, .clearNumerator, .clearDenominator,
  .countOut, .countBack, .finish]

protected theorem Control.enumList_getElem?_ctorIdx_eq (x : Control) :
    Control.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | control (phase : Control)
  | number (which : Number) (phase : ExtensionNatMachine.Label)
  | order (phase : BinaryOrderMachine.PreserveLabel)
  deriving DecidableEq, Fintype

abbrev Tape := Fin 8
abbrev Alphabet (_ : Tape) := Bool
abbrev State := BinaryAddMachine.State (Bool × Ordering)

def clean (valid : Bool) : State := BinaryAddMachine.clean (valid, .eq)

def validity (s : State) : Bool := s.1.1.1.1

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun s => clean (validity s)) (.goto fun _ => label)

def scanTape (which : Number) : Fin 3 → Tape
  | 0 => 1
  | 1 => match which with | .numerator => 3 | .denominator => 4
  | _ => 2

def scanPorts (which : Number) : Fin 3 ↪ Tape :=
  ⟨scanTape which, by
    intro i j h
    cases which <;> fin_cases i <;> fin_cases j <;> simp_all [scanTape]⟩

def orderTape : Fin 5 → Tape
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | _ => 2

def orderPorts : Fin 5 ↪ Tape :=
  ⟨orderTape, by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [orderTape]⟩

def scanSuccess : Number → Label
  | .numerator => .control .positive
  | .denominator => .order .leftOut

def orderExit : Ordering → Option Label
  | .lt | .eq => some (.control .clearNumerator)
  | .gt => some (.control .failed)

def instruction : Control → TM2.Stmt Alphabet Label State
  | .entry => .pop 0 (fun s bit => (s.1, bit))
      (.branch (fun s => s.2.getD false)
        (jump (.control .copyOut)) (jump (.control .malformedDrain)))
  | .malformedDrain => MachineDrain.drain 0 (.control .malformedDrain)
      (some (.control .malformedFinish))
  | .malformedFinish => .push 0 (fun _ => false) (.push 0 (fun _ => false)
      (.push 0 (fun _ => false) (.load (fun _ => clean true) .halt)))
  | .copyOut => loopAt 0 2 id false (.control .copyOut) (some (.control .copyBack))
  | .copyBack => MachineCopy.forkLoop 2 0 1 false (.control .copyBack)
      (some (.control .seed))
  | .seed => .push 7 (fun _ => false) (jump (.control .marker))
  | .marker => .pop 1 (fun s bit => (s.1, bit))
      (.branch (fun s => s.2.getD false)
        (.push 7 (fun _ => true) (jump (.number .numerator .scan)))
        (jump (.control .countOut)))
  | .positive => .pop 3 (fun s bit => (s.1, bit))
      (.branch (fun s => s.2.isSome)
        (.push 3 (fun s => s.2.getD false) (jump (.number .denominator .scan)))
        (.load (fun _ => clean false) (.goto fun _ => .number .denominator .scan)))
  | .failed => .load (fun _ => clean false) (.goto fun _ => .control .clearNumerator)
  | .clearNumerator => MachineDrain.drain 3 (.control .clearNumerator)
      (some (.control .clearDenominator))
  | .clearDenominator => MachineDrain.drain 4 (.control .clearDenominator)
      (some (.control .marker))
  | .countOut => loopAt 7 2 id false (.control .countOut) (some (.control .countBack))
  | .countBack => loopAt 2 0 id false (.control .countBack) (some (.control .finish))
  | .finish => .push 0 validity (.load (fun _ => clean true) .halt)

def program : Label → TM2.Stmt Alphabet Label State
  | .control phase => instruction phase
  | .number which phase => ExtensionNatMachine.statement (scanPorts which)
      (Label.number which) (some (scanSuccess which))
      (some (.control .malformedDrain)) phase
  | .order phase => ExtensionNatMachine.orderStatement orderPorts Label.order orderExit phase

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := .control .entry
  σ := State
  initialState := clean true
  m := program

def tapes (raw stream scratch numerator denominator count : List Bool) : Tape → List Bool
  | 0 => raw
  | 1 => stream
  | 2 => scratch
  | 3 => numerator
  | 4 => denominator
  | 7 => count
  | _ => []

def cfg (label : Option Label) (valid : Bool) (base : Tape → List Bool) : machine.Cfg :=
  ⟨label, clean valid, base⟩

private theorem update_raw (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 0 x = tapes x i s n d c := by
  funext k; fin_cases k <;> rfl

private theorem update_stream (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 1 x = tapes r x s n d c := by
  funext k; fin_cases k <;> rfl

private theorem update_scratch (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 2 x = tapes r i x n d c := by
  funext k; fin_cases k <;> rfl

private theorem update_numerator (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 3 x = tapes r i s x d c := by
  funext k; fin_cases k <;> rfl

private theorem update_denominator (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 4 x = tapes r i s n x c := by
  funext k; fin_cases k <;> rfl

private theorem update_count (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 7 x = tapes r i s n d x := by
  funext k; fin_cases k <;> rfl

def oneStep {start finish : machine.Cfg} (step : machine.step start = some finish) :
    StateTransition.EvalsToInTime machine.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    change machine.step start = some finish
    exact step
  steps_le_m := Nat.le_refl _

def join {start middle finish : machine.Cfg} {a b : Nat}
    (first : StateTransition.EvalsToInTime machine.step start (some middle) a)
    (second : StateTransition.EvalsToInTime machine.step middle (some finish) b) :
    StateTransition.EvalsToInTime machine.step start (some finish) (a + b) := by
  simpa only [Nat.add_comm] using StateTransition.EvalsToInTime.trans machine.step
    a b start middle (some finish) first second

def enlarge {start finish : machine.Cfg} {a b : Nat}
    (run : StateTransition.EvalsToInTime machine.step start (some finish) a)
    (bound : a ≤ b) : StateTransition.EvalsToInTime machine.step start (some finish) b where
  toEvalsTo := run.toEvalsTo
  steps_le_m := Nat.le_trans run.steps_le_m bound

theorem entryStep (flag : Bool) (raw : List Bool) :
    machine.step (cfg (some (.control .entry)) true (tapes (flag :: raw) [] [] [] [] [])) =
      some (cfg (some (.control (if flag then .copyOut else .malformedDrain))) true
        (tapes raw [] [] [] [] [])) := by
  change some (TM2.stepAux (program (.control .entry)) (clean true)
    (tapes (flag :: raw) [] [] [] [] [])) = _
  cases flag <;>
    simp [program, instruction, jump, cfg, clean, validity, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, tapes, update_raw] <;> rfl

theorem markerStep (valid flag : Bool) (raw stream count : List Bool) :
    machine.step (cfg (some (.control .marker)) valid
      (tapes raw (flag :: stream) [] [] [] count)) =
      some (cfg (some (if flag then .number .numerator .scan else .control .countOut))
        valid (tapes raw stream [] [] [] (if flag then true :: count else count))) := by
  change some (TM2.stepAux (program (.control .marker)) (clean valid)
    (tapes raw (flag :: stream) [] [] [] count)) = _
  cases flag <;>
    simp [program, instruction, jump, cfg, clean, validity, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, tapes, update_stream, update_count] <;> rfl

theorem positiveStep (valid : Bool) (raw stream numerator count : List Bool) :
    machine.step (cfg (some (.control .positive)) valid
      (tapes raw stream [] numerator [] count)) =
      some (cfg (some (.number .denominator .scan))
        (valid && decide (numerator ≠ [])) (tapes raw stream [] numerator [] count)) := by
  change some (TM2.stepAux (program (.control .positive)) (clean valid)
    (tapes raw stream [] numerator [] count)) = _
  cases numerator <;>
    simp [program, instruction, jump, cfg, clean, validity, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, tapes, update_numerator] <;> rfl

def numeratorInTime (valid : Bool) (raw suffix count : List Bool) (n : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.number .numerator .scan)) valid
        (tapes raw (BinaryEncoding.natBits n ++ suffix) [] [] [] count))
      (some (cfg (some (.control .positive)) valid (tapes raw suffix [] n.bits [] count)))
      (2 * n.size + 2) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.number .numerator .scan), BinaryAddMachine.clean (valid, .eq),
      tapes raw (BinaryEncoding.natBits n ++ suffix) [] [] [] count⟩
    (some ⟨some (.control .positive), BinaryAddMachine.clean (valid, .eq),
      tapes raw suffix [] n.bits [] count⟩) _
  have result : ExtensionNatMachine.resultTapes (scanPorts .numerator)
      (tapes raw (BinaryEncoding.natBits n ++ suffix) [] [] [] count) n suffix =
      tapes raw suffix [] n.bits [] count := by
    simp only [scanPorts]
    funext k
    fin_cases k <;> first | rfl | exact List.append_nil _
  simpa only [cfg, result, scanSuccess] using!
    ExtensionNatMachine.natInTime (scanPorts .numerator) (Label.number .numerator)
      (some (scanSuccess .numerator)) (some (.control .malformedDrain)) program
      (fun _ => rfl) (tapes raw (BinaryEncoding.natBits n ++ suffix) [] [] [] count)
      n suffix rfl rfl (valid, .eq)

def denominatorInTime (valid : Bool) (raw suffix count : List Bool) (n d : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.number .denominator .scan)) valid
        (tapes raw (BinaryEncoding.natBits d ++ suffix) [] n.bits [] count))
      (some (cfg (some (.order .leftOut)) valid (tapes raw suffix [] n.bits d.bits count)))
      (2 * d.size + 2) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.number .denominator .scan), BinaryAddMachine.clean (valid, .eq),
      tapes raw (BinaryEncoding.natBits d ++ suffix) [] n.bits [] count⟩
    (some ⟨some (.order .leftOut), BinaryAddMachine.clean (valid, .eq),
      tapes raw suffix [] n.bits d.bits count⟩) _
  have result : ExtensionNatMachine.resultTapes (scanPorts .denominator)
      (tapes raw (BinaryEncoding.natBits d ++ suffix) [] n.bits [] count) d suffix =
      tapes raw suffix [] n.bits d.bits count := by
    simp only [scanPorts]
    funext k
    fin_cases k <;> first | rfl | exact List.append_nil _
  simpa only [cfg, result, scanSuccess] using!
    ExtensionNatMachine.natInTime (scanPorts .denominator) (Label.number .denominator)
      (some (scanSuccess .denominator)) (some (.control .malformedDrain)) program
      (fun _ => rfl) (tapes raw (BinaryEncoding.natBits d ++ suffix) [] n.bits [] count)
      d suffix rfl rfl (valid, .eq)

theorem bits_eq_nil_iff (n : Nat) : n.bits = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := congrArg BinPackingCompleteness.BinaryEncoding.bitsValue h
    simpa only [BinPackingCompleteness.BinaryEncoding.bitsValue_bits,
      BinPackingCompleteness.BinaryEncoding.bitsValue] using hv
  · rintro rfl; rfl

def comparisonInTime (valid : Bool) (raw stream count : List Bool) (a d : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.order .leftOut)) valid (tapes raw stream [] a.bits d.bits count))
      (some (cfg (some (.control .clearNumerator)) (valid && decide (a ≤ d))
        (tapes raw stream [] a.bits d.bits count)))
      (BinaryOrderMachine.preservingSteps a.size d.size + 1) := by
  have trace := ExtensionNatMachine.preservingOrderInTime orderPorts Label.order orderExit
    program (fun _ => rfl) (tapes raw stream [] a.bits d.bits count) a d
    rfl rfl rfl rfl rfl valid
  have exit : orderExit (BinaryOrderMachine.orderNat a d .eq) =
      some (.control (if a ≤ d then .clearNumerator else .failed)) := by
    unfold BinaryOrderMachine.orderNat
    split_ifs <;> simp_all [orderExit] <;> omega
  rw [exit] at trace
  by_cases h : a ≤ d
  · simpa only [h, ite_true, decide_true, Bool.and_true, cfg, clean] using
      enlarge (b := BinaryOrderMachine.preservingSteps a.size d.size + 1) trace (by omega)
  · have failure : machine.step (cfg (some (.control .failed)) valid
        (tapes raw stream [] a.bits d.bits count)) =
        some (cfg (some (.control .clearNumerator)) false
          (tapes raw stream [] a.bits d.bits count)) := by rfl
    simp only [h, ite_false] at trace
    simpa only [h, ite_false, decide_false, Bool.and_false, cfg, clean] using
      join trace (oneStep failure)

def clearInTime (valid : Bool) (raw stream numerator denominator count : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.control .clearNumerator)) valid
        (tapes raw stream [] numerator denominator count))
      (some (cfg (some (.control .marker)) valid (tapes raw stream [] [] [] count)))
      (numerator.length + denominator.length + 2) := by
  have first := MachineDrain.drainInTime (3 : Tape) (.control .clearNumerator)
    (some (.control .clearDenominator)) program rfl
    (tapes raw stream [] numerator denominator count) (((valid, Ordering.eq), false), none) none
  have second := MachineDrain.drainInTime (4 : Tape) (.control .clearDenominator)
    (some (.control .marker)) program rfl
    (tapes raw stream [] [] denominator count) (((valid, Ordering.eq), false), none) none
  simp only [update_numerator, tapes] at first
  simp only [update_denominator, tapes] at second
  have both := join first second
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.control .clearNumerator), BinaryAddMachine.clean (valid, .eq),
      tapes raw stream [] numerator denominator count⟩
    (some ⟨some (.control .marker), BinaryAddMachine.clean (valid, .eq),
      tapes raw stream [] [] [] count⟩) _
  exact { toEvalsTo := both.toEvalsTo
          steps_le_m := by
            have bound := both.steps_le_m
            omega }

def rowTime (a d : Nat) : Nat := 6 * (a.size + d.size) + 14

def loopTime : RawInstance → Nat
  | [] => 1
  | (a, d) :: items => rowTime a d + loopTime items

theorem validItems_cons (a d : Nat) (items : RawInstance) :
    ExtensionCertificate.validItems ((a, d) :: items) =
      (decide (0 < a) && decide (a ≤ d) && ExtensionCertificate.validItems items) := by
  simp [ExtensionCertificate.validItems, Bool.and_assoc]

def itemsInTime (items : RawInstance) (valid : Bool) (raw : List Bool) (count : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.control .marker)) valid
        (tapes raw (BinaryEncoding.rawInstanceBits items) [] [] [] (encodeWord count)))
      (some (cfg (some (.control .countOut))
        (valid && ExtensionCertificate.validItems items)
        (tapes raw [] [] [] [] (encodeWord (count + items.length)))))
      (loopTime items) := by
  induction items generalizing valid count with
  | nil =>
      simpa [loopTime, ExtensionCertificate.validItems,
        BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits] using
        oneStep (markerStep valid false raw [] (encodeWord count))
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      have marker := oneStep (markerStep valid true raw
        (BinaryEncoding.natBits a ++ BinaryEncoding.natBits d ++
          BinaryEncoding.rawInstanceBits items) (encodeWord count))
      have numerator := numeratorInTime valid raw
        (BinaryEncoding.natBits d ++ BinaryEncoding.rawInstanceBits items)
        (encodeWord (count + 1)) a
      have positive := oneStep (positiveStep valid raw
        (BinaryEncoding.natBits d ++ BinaryEncoding.rawInstanceBits items) a.bits
        (encodeWord (count + 1)))
      have nonempty : decide (a.bits ≠ []) = decide (0 < a) := by
        simp only [ne_eq, bits_eq_nil_iff, Nat.pos_iff_ne_zero]
      rw [nonempty] at positive
      have denominator := denominatorInTime (valid && decide (0 < a)) raw
        (BinaryEncoding.rawInstanceBits items) (encodeWord (count + 1)) a d
      have comparison := comparisonInTime (valid && decide (0 < a)) raw
        (BinaryEncoding.rawInstanceBits items) (encodeWord (count + 1)) a d
      have clear := clearInTime (valid && decide (0 < a) && decide (a ≤ d)) raw
        (BinaryEncoding.rawInstanceBits items) a.bits d.bits (encodeWord (count + 1))
      have rest := ih (valid && decide (0 < a) && decide (a ≤ d)) (count + 1)
      have count_succ : true :: encodeWord count = encodeWord (count + 1) := by
        simp [encodeWord, List.replicate_succ]
      rw [count_succ] at marker
      simp only [List.append_assoc] at marker
      have trace := join (join (join (join (join (join marker numerator) positive)
        denominator) comparison) clear) rest
      have bounded : 1 + (2 * a.size + 2) + 1 + (2 * d.size + 2) +
          (BinaryOrderMachine.preservingSteps a.size d.size + 1) +
          (a.bits.length + d.bits.length + 2) + loopTime items ≤
          loopTime ((a, d) :: items) := by
        have h := BinaryOrderMachine.preservingSteps_le a.size d.size
        simp only [loopTime, rowTime, Nat.size_eq_bits_len]
        omega
      simpa only [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits,
        BinaryEncoding.pairBits, List.length_cons, List.append_assoc,
        validItems_cons, Bool.and_assoc, Nat.add_assoc, Nat.add_comm 1 items.length] using
        enlarge trace bounded

theorem loopTime_le (items : RawInstance) :
    loopTime items ≤ 5 * (BinaryEncoding.rawInstanceBits items).length := by
  induction items with
  | nil => simp [loopTime, BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits]
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      have length : (BinaryEncoding.rawInstanceBits ((a, d) :: items)).length =
          2 * a.size + 2 * d.size + 3 + (BinaryEncoding.rawInstanceBits items).length := by
        simp only [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits,
          BinaryEncoding.pairBits, List.length_cons, List.length_append,
          BinaryEncoding.natBits_length]
        omega
      rw [length]
      simp only [loopTime, rowTime]
      omega

def copyInTime (raw : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.control .copyOut)) true (tapes raw [] [] [] [] []))
      (some (cfg (some (.control .seed)) true (tapes raw raw [] [] [] [])))
      (2 * (raw.length + 1)) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.control .copyOut), BinaryAddMachine.clean (true, .eq),
      tapes raw [] [] [] [] []⟩
    (some ⟨some (.control .seed), BinaryAddMachine.clean (true, .eq),
      tapes raw raw [] [] [] []⟩) _
  simpa only [cfg, clean, BinaryAddMachine.clean, BinaryAddMachine.state,
    update_stream, tapes, List.append_nil] using
    MachineCopy.copyInTime (0 : Tape) 1 2 (by decide) (by decide) (by decide)
      false (.control .copyOut) (.control .copyBack) (some (.control .seed)) program
      rfl rfl (tapes raw [] [] [] [] []) rfl (((true, Ordering.eq), false), none) none

theorem seedStep (raw : List Bool) :
    machine.step (cfg (some (.control .seed)) true (tapes raw raw [] [] [] [])) =
      some (cfg (some (.control .marker)) true (tapes raw raw [] [] [] (encodeWord 0))) := by
  change some (TM2.stepAux (program (.control .seed)) (clean true)
    (tapes raw raw [] [] [] [])) = _
  simp [program, instruction, jump, cfg, clean, validity, BinaryAddMachine.clean,
    BinaryAddMachine.state, TM2.stepAux, tapes, update_count, encodeWord]
  rfl

def countInTime (valid : Bool) (raw : List Bool) (count : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.control .countOut)) valid (tapes raw [] [] [] [] (encodeWord count)))
      (some (cfg (some (.control .finish)) valid
        (tapes (encodeWord count ++ raw) [] [] [] [] [])))
      (2 * (count + 2)) := by
  have first := transferAtInTime (7 : Tape) 2 (by decide) id false
    (.control .countOut) (some (.control .countBack)) program rfl
    (tapes raw [] [] [] [] (encodeWord count)) (((valid, Ordering.eq), false), none) none
  simp only [tapesAt, update_count, update_scratch, tapes, List.map_id_fun, id_eq,
    List.append_nil] at first
  have second := transferAtInTime (2 : Tape) 0 (by decide) id false
    (.control .countBack) (some (.control .finish)) program rfl
    (tapes raw [] (encodeWord count).reverse [] [] [])
    (((valid, Ordering.eq), false), none) none
  simp only [tapesAt, update_scratch, update_raw, tapes, List.map_id_fun, id_eq,
    List.reverse_reverse, List.length_reverse] at second
  have length : (encodeWord count).length = count + 1 := by simp [encodeWord]
  have both := join first second
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.control .countOut), BinaryAddMachine.clean (valid, .eq),
      tapes raw [] [] [] [] (encodeWord count)⟩
    (some ⟨some (.control .finish), BinaryAddMachine.clean (valid, .eq),
      tapes (encodeWord count ++ raw) [] [] [] [] []⟩) _
  exact { toEvalsTo := both.toEvalsTo
          steps_le_m := by
            have bound := both.steps_le_m
            simp only [length] at bound
            omega }

theorem finishStep (valid : Bool) (output : List Bool) :
    machine.step (cfg (some (.control .finish)) valid (tapes output [] [] [] [] [])) =
      some (cfg none true (tapes (valid :: output) [] [] [] [] [])) := by
  change some (TM2.stepAux (program (.control .finish)) (clean valid)
    (tapes output [] [] [] [] [])) = _
  simp [program, instruction, cfg, clean, validity, BinaryAddMachine.clean,
    BinaryAddMachine.state, TM2.stepAux, tapes, update_raw]
  rfl

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some (.control .entry)) true (tapes input [] [] [] [] []) := by
  unfold initList cfg
  congr 1
  funext k; fin_cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none true (tapes output [] [] [] [] []) := by
  unfold haltList cfg
  congr 1
  funext k; fin_cases k <;> rfl

theorem item_count_le (items : RawInstance) :
    items.length ≤ (BinaryEncoding.rawInstanceBits items).length := by
  induction items with
  | nil => simp
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      simp only [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits,
        BinaryEncoding.pairBits, List.length_cons, List.length_append] at ih ⊢
      omega

def encodedInTime (items : RawInstance) :
    TM2OutputsInTime machine (true :: BinaryEncoding.rawInstanceBits items)
      (some (dataBits (items, ExtensionCertificate.validItems items)))
      (16 * ((BinaryEncoding.rawInstanceBits items).length + 2)) := by
  have entry := oneStep (entryStep true (BinaryEncoding.rawInstanceBits items))
  have copy := copyInTime (BinaryEncoding.rawInstanceBits items)
  have seed := oneStep (seedStep (BinaryEncoding.rawInstanceBits items))
  have loop := itemsInTime items true (BinaryEncoding.rawInstanceBits items) 0
  simp only [Bool.true_and, Nat.zero_add] at loop
  have count := countInTime (ExtensionCertificate.validItems items)
    (BinaryEncoding.rawInstanceBits items) items.length
  have finish := oneStep (finishStep (ExtensionCertificate.validItems items)
    (encodeWord items.length ++ BinaryEncoding.rawInstanceBits items))
  have trace := join (join (join (join (join entry copy) seed) loop) count) finish
  have bounded : 1 + 2 * ((BinaryEncoding.rawInstanceBits items).length + 1) + 1 +
      loopTime items + 2 * (items.length + 2) + 1 ≤
      16 * ((BinaryEncoding.rawInstanceBits items).length + 2) := by
    have loopBound := loopTime_le items
    have countBound := item_count_le items
    omega
  change StateTransition.EvalsToInTime machine.step
    (initList machine (true :: BinaryEncoding.rawInstanceBits items))
    (some (haltList machine (dataBits (items, ExtensionCertificate.validItems items)))) _
  rw [initList_eq, haltList_eq]
  exact enlarge trace bounded

def malformedInTime (raw : List Bool) :
    TM2OutputsInTime machine (false :: raw) (some (dataBits ([], false)))
      (16 * (raw.length + 2)) := by
  have entry := oneStep (entryStep false raw)
  have drain := MachineDrain.drainInTime (0 : Tape) (.control .malformedDrain)
    (some (.control .malformedFinish)) program rfl (tapes raw [] [] [] [] [])
    (((true, Ordering.eq), false), none) none
  simp only [update_raw, tapes] at drain
  have finish : machine.step (cfg (some (.control .malformedFinish)) true
      (tapes [] [] [] [] [] [])) =
      some (cfg none true (tapes (dataBits ([], false)) [] [] [] [] [])) := by
    change some (TM2.stepAux (program (.control .malformedFinish)) (clean true)
      (tapes [] [] [] [] [] [])) = _
    simp [program, instruction, cfg, dataBits, encodeWord, BinaryEncoding.rawInstanceBits,
      BinaryEncoding.listBits, TM2.stepAux, update_raw, tapes]
    rfl
  have trace := join (join entry drain) (oneStep finish)
  change StateTransition.EvalsToInTime machine.step
    (initList machine (false :: raw)) (some (haltList machine (dataBits ([], false)))) _
  rw [initList_eq, haltList_eq]
  exact enlarge trace (by omega)

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine (shapeBits input) (some (dataBits (classify input)))
      (16 * ((shapeBits input).length + 1)) := by
  cases parsed : BinaryEncoding.decodeRawInstance input with
  | none =>
      simpa only [shapeBits, classify, parsed, Option.isSome_none, List.length_cons]
        using malformedInTime input
  | some items =>
      have encoded := BinaryEncoding.decodeRawInstance_sound parsed
      subst input
      simpa only [shapeBits, classify, BinaryEncoding.decodeRawInstance_rawInstanceBits,
        Option.isSome_some, List.length_cons] using encodedInTime items

noncomputable def computation : TM2ComputableInPolyTime shapeBits dataBits classify where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 16 * (Polynomial.X + 1)
  outputsFun input := by
    change TM2OutputsInTime machine ((shapeBits input).map id)
      (some ((dataBits (classify input)).map id))
      ((16 * (Polynomial.X + 1) : Polynomial Nat).eval (shapeBits input).length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one] using outputsInTime input

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm := by
  intro k
  change Finite Bool
  infer_instance

end BinPackingGap.SearchInitialItemsMachine

end OAI
