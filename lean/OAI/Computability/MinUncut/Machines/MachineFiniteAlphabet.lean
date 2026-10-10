import Mathlib
import OAI.Computability.MinUncut.Machines.LoopInitialization

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

def FiniteAlphabet (M : FinTM2) : Prop := ∀ k, Finite (M.Γ k)

theorem input_finite (M : FinTM2) : Finite (M.Γ M.k₀) := by
  let := M.Γk₀Fin
  infer_instance

theorem of_homogeneous (M : FinTM2) {α : Type} [Finite α]
    (alphabet : ∀ k, M.Γ k = α) : FiniteAlphabet M := by
  intro k
  rw [alphabet k]
  infer_instance

theorem of_bool (M : FinTM2) (alphabet : ∀ k, M.Γ k = Bool) : FiniteAlphabet M :=
  of_homogeneous M alphabet

theorem of_equiv (M : FinTM2) {α : Type} [Finite α]
    (alphabet : ∀ k, M.Γ k ≃ α) : FiniteAlphabet M := by
  intro k
  exact Finite.of_equiv α (alphabet k).symm

theorem symbols_finite (M : FinTM2) (finiteAlphabet : FiniteAlphabet M) :
    Finite (Σ k, M.Γ k) := by
  let := M.kFin
  let : ∀ k, Finite (M.Γ k) := finiteAlphabet
  infer_instance

theorem sequential_machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (hfirst : FiniteAlphabet first) (hsecond : FiniteAlphabet second) :
    FiniteAlphabet (MachineSequential.machine first second relabel fallback) := by
  intro tape
  rcases tape with tape | tape | tape
  · exact hfirst tape
  · exact hsecond tape
  · exact input_finite second

theorem compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.compose first second fallback).tm := by
  exact sequential_machine first.tm second.tm
    (fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol))
    (second.inputAlphabet.symm fallback) hfirst hsecond

theorem composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.composeBits first second).tm :=
  compose first second false hfirst hsecond

theorem repeat_machine (body : FinTM2)
    (input : body.Γ body.k₀ ≃ Bool) (output : body.Γ body.k₁ ≃ Bool)
    (hbody : FiniteAlphabet body) :
    FiniteAlphabet (MachineRepeat.machine body input output) := by
  intro tape
  cases tape with
  | inl tape => exact hbody tape
  | inr _ => exact input_finite body

end MinUncutGames.Foundations.Complexity.MachineFiniteAlphabet

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable

open MinUncutGames.Foundations.Complexity

theorem Driver.finiteAlphabet (q : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (Driver.machine q) := by
  intro k
  change Finite Bool
  infer_instance

theorem Runtime.finiteAlphabet (q : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (Runtime.tablePolynomialTime q).tm :=
  Driver.finiteAlphabet q

end MinUncutGames.Foundations.PCP.AlphabetTable

end
section
namespace MinUncutGames.Foundations.Complexity.MachineStateEquiv

open Turing.TM2

variable {K Λ σ τ : Type} {Γ : K → Type}

abbrev statement (e : σ ≃ τ) : Stmt Γ Λ σ → Stmt Γ Λ τ :=
  MachineControl.statement (id : Λ → Λ) e

@[simp] theorem statement_symm_statement (e : σ ≃ τ) (q : Stmt Γ Λ σ) :
    statement e.symm (statement e q) = q := by
  induction q <;>
    simp_all only [statement, MachineControl.statement, Equiv.symm_symm,
      Equiv.symm_apply_apply, id_eq]

def configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) : Cfg Γ Λ τ :=
  ⟨c.l, e c.var, c.stk⟩

@[simp] theorem configuration_label (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).l = c.l := rfl

@[simp] theorem configuration_state (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).var = e c.var := rfl

@[simp] theorem configuration_tapes (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).stk = c.stk := rfl

@[simp] theorem configuration_symm_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configuration e.symm (configuration e c) = c := by
  cases c
  simp only [configuration, Equiv.symm_apply_apply]

@[simp] theorem configuration_configuration_symm (e : σ ≃ τ) (c : Cfg Γ Λ τ) :
    configuration e (configuration e.symm c) = c := by
  cases c
  simp only [configuration, Equiv.apply_symm_apply]

def configurationEquiv (e : σ ≃ τ) : Cfg Γ Λ σ ≃ Cfg Γ Λ τ where
  toFun := configuration e
  invFun := configuration e.symm
  left_inv := configuration_symm_configuration e
  right_inv := configuration_configuration_symm e

@[simp] theorem configurationEquiv_apply (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configurationEquiv e c = configuration e c := rfl

@[simp] theorem control_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    MachineControl.configuration (id : Λ → Λ) e c = configuration e c := by
  cases c
  simp [MachineControl.configuration, configuration]

def program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Γ Λ τ :=
  fun l => statement e (source l)

@[simp] theorem program_symm_program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) :
    program e.symm (program e source) = source := by
  funext l
  exact statement_symm_statement e (source l)

theorem statementPushBound (e : σ ≃ τ) (q : Stmt Γ Λ σ) :
    Runtime.statementPushBound (statement e q) = Runtime.statementPushBound q := by
  induction q <;>
    simp_all only [statement, MachineControl.statement, Runtime.statementPushBound]

theorem supportsStmt_iff (e : σ ≃ τ) (S : Finset Λ) (q : Stmt Γ Λ σ) :
    SupportsStmt S (statement e q) ↔ SupportsStmt S q := by
  induction q with
  | push k f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | peek k f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | pop k f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | load f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | branch f yes no ihYes ihNo =>
      simp only [statement, MachineControl.statement, SupportsStmt, ihYes, ihNo]
  | goto f =>
      change (∀ state : τ, f (e.symm state) ∈ S) ↔ ∀ state : σ, f state ∈ S
      constructor
      · intro h state
        simpa only [Equiv.symm_apply_apply] using h (e state)
      · intro h state
        exact h (e.symm state)
  | halt => rfl

theorem supports_iff [Inhabited Λ] (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    (S : Finset Λ) : Supports (program e source) S ↔ Supports source S := by
  simp only [Supports, program, supportsStmt_iff]

variable [DecidableEq K]

theorem stepAux_transport (e : σ ≃ τ) (q : Stmt Γ Λ σ) (state : σ)
    (tapes : ∀ k, List (Γ k)) :
    stepAux (statement e q) (e state) tapes =
      configuration e (stepAux q state tapes) := by
  simpa only [statement, control_configuration] using
    MachineControl.stepAux_simulation (id : Λ → Λ) e q state tapes

theorem stepAux_transport_symm (e : σ ≃ τ) (q : Stmt Γ Λ σ) (state : τ)
    (tapes : ∀ k, List (Γ k)) :
    stepAux (statement e q) state tapes =
      configuration e (stepAux q (e.symm state) tapes) := by
  simpa only [Equiv.apply_symm_apply] using
    stepAux_transport e q (e.symm state) tapes

theorem step_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (program e source) (configuration e c) =
      (step source c).map (configuration e) := by
  cases c with
  | mk l state tapes =>
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (statement e (source l)) (e state) tapes) = _
          rw [stepAux_transport]
          rfl

theorem step_iff (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (a b : Cfg Γ Λ σ) :
    step (program e source) (configuration e a) = some (configuration e b) ↔
      step source a = some b := by
  rw [step_transport]
  change (step source a).map (configuration e) = (some b).map (configuration e) ↔ _
  constructor
  · intro h
    apply Option.map_injective (configurationEquiv e).injective
    change (step source a).map (configuration e) = (some b).map (configuration e)
    exact h
  · exact congrArg (Option.map (configuration e))

theorem advance_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    (c : Option (Cfg Γ Λ σ)) :
    MachineComposition.advance (step (program e source)) (c.map (configuration e)) =
      (MachineComposition.advance (step source) c).map (configuration e) := by
  cases c with
  | none => rfl
  | some c => exact step_transport e source c

theorem iterate_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (c : Option (Cfg Γ Λ σ)) :
    (MachineComposition.advance (step (program e source)))^[n]
        (c.map (configuration e)) =
      ((MachineComposition.advance (step source))^[n] c).map (configuration e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, advance_transport,
        Function.iterate_succ_apply']

theorem trace_iff (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (a b : Cfg Γ Λ σ) :
    (MachineComposition.advance (step (program e source)))^[n]
        (some (configuration e a)) = some (configuration e b) ↔
      (MachineComposition.advance (step source))^[n] (some a) = some b := by
  change (MachineComposition.advance (step (program e source)))^[n]
      ((some a).map (configuration e)) = (some b).map (configuration e) ↔ _
  rw [iterate_transport]
  constructor
  · intro h
    apply Option.map_injective (configurationEquiv e).injective
    change ((MachineComposition.advance (step source))^[n] (some a)).map (configuration e) =
      (some b).map (configuration e)
    exact h
  · exact congrArg (Option.map (configuration e))

theorem trace (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (a b : Cfg Γ Λ σ)
    (run : (MachineComposition.advance (step source))^[n] (some a) = some b) :
    (MachineComposition.advance (step (program e source)))^[n]
      (some (configuration e a)) = some (configuration e b) :=
  (trace_iff e source n a b).2 run

def execution (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (step (program e source)))^[run.steps]
      ((some start).map (configuration e)) = finish.map (configuration e)
    rw [iterate_transport, h]
  steps_le_m := run.steps_le_m

@[simp] theorem execution_steps (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    (execution e source run).steps = run.steps := rfl

def execution_reflect (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget) :
    StateTransition.EvalsToInTime (step source) start finish budget where
  steps := run.steps
  evals_in_steps := by
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish
    apply Option.map_injective (configurationEquiv e).injective
    change ((MachineComposition.advance (step source))^[run.steps] (some start)).map
      (configuration e) = finish.map (configuration e)
    rw [← iterate_transport]
    exact run.evals_in_steps
  steps_le_m := run.steps_le_m

@[simp] theorem execution_reflect_steps (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget) :
    (execution_reflect e source run).steps = run.steps := rfl

end MinUncutGames.Foundations.Complexity.MachineStateEquiv

end
section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryAffineAt

open Turing
open MachineComposition
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (restoreLabel : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun s => (s.1,none)) (.goto (fun _ => restoreLabel))

def scan (source scratch destination : K) (coefficient : Nat) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun s head => (s.1,head))
    (.branch (fun s => s.2.getD false)
      (.push scratch (fun _ => true)
        (pushWord destination (List.replicate coefficient true) (.goto (fun _ => scanLabel))))
      (.branch (fun s => s.2.isSome)
        (.push source (fun _ => false) (finish restoreLabel))
        (finish restoreLabel)))

def seed (destination : K) (offset : Nat) (scanLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  pushWord destination (encodeWord offset).reverse (.goto (fun _ => scanLabel))

def tapes (source scratch destination : K) (base : K → List Bool)
    (input saved output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input saved output

@[simp] theorem tapes_source (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output source = input :=
  MachineCopy.forkTapes_source source scratch destination hs hd base input saved output

@[simp] theorem tapes_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output scratch = saved :=
  MachineCopy.forkTapes_left source scratch destination hsd base input saved output

@[simp] theorem tapes_destination (source scratch destination : K)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output destination = output :=
  MachineCopy.forkTapes_right source scratch destination base input saved output

theorem update_source (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) source replacement =
      tapes source scratch destination base replacement saved output := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k; simp [tapes, MachineCopy.forkTapes, h₀, hsd]
    · by_cases h₂ : k = destination
      · subst k; simp [tapes, MachineCopy.forkTapes, h₀]
      · simp [tapes, MachineCopy.forkTapes, h₀, h₁, h₂]

theorem update_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) scratch replacement =
      tapes source scratch destination base input replacement output := by
  funext k
  by_cases h : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, hsd]
  · by_cases h' : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, h]
    · simp [tapes, MachineCopy.forkTapes, h, h']

theorem update_destination (source scratch destination : K)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) destination replacement =
      tapes source scratch destination base input saved replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem prepend_replicate_word (c b : Nat) (suffix : List Bool) :
    List.replicate c true ++ (encodeWord b ++ suffix) =
      encodeWord (c + b) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

theorem scan_step_succ (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord (a + 1) ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some scanLabel, (ambient,some true), tapes source scratch destination base
        (encodeWord a ++ suffix) (true :: saved) (encodeWord (coefficient + b) ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord (a + 1) ++ suffix = true :: (encodeWord a ++ suffix) by
    simp [encodeWord, List.replicate_succ]]
  simp [scan, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source source scratch destination hs hd hsd, tapes_scratch _ _ _ hsd,
    update_scratch _ _ _ hsd, stepAux_pushWord, tapes_destination,
    prepend_replicate_word, update_destination]

theorem scan_step_zero (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord 0 ++ suffix = false :: suffix from rfl]
  simp [scan, finish, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source source scratch destination hs hd hsd]

theorem scanTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[a + 1]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) saved (encodeWord b ++ output)⟩) =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) (List.replicate a true ++ saved)
        (encodeWord (coefficient * a + b) ++ output)⟩ := by
  induction a generalizing b saved register with
  | zero =>
      simpa using scan_step_zero source scratch destination hs hd hsd coefficient scanLabel
        restoreLabel program atScan base b suffix saved output ambient register
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ source scratch destination hs hd hsd coefficient scanLabel restoreLabel
        program atScan]
      rw [ih]
      have hval : coefficient * a + (coefficient + b) = coefficient * (a + 1) + b := by
        rw [Nat.mul_succ]; omega
      rw [hval]
      have hsave : List.replicate a true ++ true :: saved = List.replicate (a + 1) true ++ saved := by
        simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]
      rw [hsave]

theorem restoreTapes (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (a value : Nat) (suffix output : List Bool) :
    Reduction.MachineTransfer.tapesAt scratch source
      (tapes source scratch destination base (encodeWord 0 ++ suffix)
        (List.replicate a true) (encodeWord value ++ output))
      [] (encodeWord a ++ suffix) =
      tapes source scratch destination base (encodeWord a ++ suffix) [] (encodeWord value ++ output) := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k
      simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hs, hsd]
    · by_cases h₂ : k = destination
      · subst k
        simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hd, Ne.symm hsd]
      · simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, h₀, h₁, h₂]

theorem affineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a b : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1)]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord b ++ output)⟩) =
      some ⟨exit, (ambient,none), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord (coefficient * a + b) ++ output)⟩ := by
  have hscan := scanTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    program atScan base a b suffix [] output ambient register
  simp only [List.append_nil] at hscan
  let mid := tapes source scratch destination base (encodeWord 0 ++ suffix)
    (List.replicate a true) (encodeWord (coefficient * a + b) ++ output)
  have hrestore := Reduction.MachineTransfer.transferAt_fromTapes scratch source (Ne.symm hs)
    id false restoreLabel exit program atRestore mid ambient none
  change (advance (TM2.step program))^[(mid scratch).length + 1]
    (some ⟨some restoreLabel,(ambient,none),mid⟩) = _ at hrestore
  have hsaved : mid scratch = List.replicate a true := by
    simp [mid, tapes, hsd]
  have hsource : mid source = encodeWord 0 ++ suffix := by
    simp [mid, tapes, hs, hd]
  rw [hsaved, hsource] at hrestore
  simp only [List.length_replicate, List.reverse_replicate, List.map_id] at hrestore
  have hword : List.replicate a true ++ (encodeWord 0 ++ suffix) = encodeWord a ++ suffix := by
    simp [encodeWord, List.append_assoc]
  rw [hword] at hrestore
  simp only [mid, restoreTapes source scratch destination hs hd hsd] at hrestore
  rw [show 2 * (a + 1) = (a + 1) + (a + 1) by omega, Function.iterate_add_apply, hscan]
  exact hrestore

def affineInTime (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a b : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord b ++ output)⟩
      (some ⟨exit, (ambient,none), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord (coefficient * a + b) ++ output)⟩)
      (2 * (a + 1)) where
  steps := 2 * (a + 1)
  evals_in_steps := affineTrace source scratch destination hs hd hsd coefficient scanLabel
    restoreLabel exit program atScan atRestore base a b suffix output ambient register
  steps_le_m := Nat.le_refl _

theorem seededAffineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient offset : Nat) (seedLabel scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atSeed : program seedLabel = seed destination offset scanLabel)
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord a ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1) + 1]
      (some ⟨some seedLabel, (ambient,register), base⟩) =
      some ⟨exit, (ambient,none),
        Function.update base destination (encodeWord (coefficient * a + offset) ++ base destination)⟩ := by
  have hseed : TM2.step program ⟨some seedLabel,(ambient,register),base⟩ =
      some ⟨some scanLabel,(ambient,register),
        Function.update base destination (encodeWord offset ++ base destination)⟩ := by
    change some (TM2.stepAux (program seedLabel) _ _) = _
    rw [atSeed, seed, stepAux_pushWord]
    simp only [List.reverse_reverse, TM2.stepAux]
  have hrun := affineTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    exit program atScan atRestore base a offset suffix (base destination) ambient register
  have hframe (word : List Bool) :
      tapes source scratch destination base (encodeWord a ++ suffix) [] word =
        Function.update base destination word := by
    rw [← sourceWord, ← scratchEmpty]
    simp only [tapes, MachineCopy.forkTapes, Function.update_eq_self]
  rw [hframe, hframe] at hrun
  rw [Function.iterate_succ_apply]
  simp only [advance_some]
  rw [hseed]
  exact hrun

inductive Label
  | seed | scan | restore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seed, .scan, .restore]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def program (source scratch destination : K) (coefficient offset : Nat) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .seed => seed destination offset .scan
  | .scan => scan source scratch destination coefficient .scan .restore
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false .restore none

def machine (coefficient offset : Nat) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .seed
  σ := Unit × Option Bool
  initialState := ((),none)
  m := program 0 1 2 coefficient offset

end MinUncutGames.Foundations.Complexity.MachineUnaryAffineAt

end
section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryEqualityBit

open Turing
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Bool × Option Bool) × Option Bool

def clean (ambient : A) : State A := ((ambient, false, none), none)

def compareStateEquiv (A : Type) : MachineCompare.State A ≃ State A where
  toFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  invFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

inductive Label
  | seedLeft | scanLeft | restoreLeft
  | seedRight | scanRight | restoreRight
  | compare | equal | different
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seedLeft, .scanLeft, .restoreLeft, .seedRight,
  .scanRight, .restoreRight, .compare, .equal, .different]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def bitEncoding (bit : Bool) : List Bool := encodeWord (if bit then 1 else 0)

def emit (destination : K) (bit : Bool) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (if bit then .push destination (fun _ => true) (exitAt exit) else exitAt exit)

def instruction (tape : Fin 6 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .seedLeft => MachineUnaryAffineAt.seed (tape 2) 0 (labels .scanLeft)
  | .scanLeft => MachineUnaryAffineAt.scan (tape 0) (tape 4) (tape 2) 1
      (labels .scanLeft) (labels .restoreLeft)
  | .restoreLeft => Reduction.MachineTransfer.loopAt (tape 4) (tape 0) id false
      (labels .restoreLeft) (some (labels .seedRight))
  | .seedRight => MachineUnaryAffineAt.seed (tape 3) 0 (labels .scanRight)
  | .scanRight => MachineUnaryAffineAt.scan (tape 1) (tape 4) (tape 3) 1
      (labels .scanRight) (labels .restoreRight)
  | .restoreRight => Reduction.MachineTransfer.loopAt (tape 4) (tape 1) id false
      (labels .restoreRight) (some (labels .compare))
  | .compare => MachineStateEquiv.statement (compareStateEquiv A)
      (MachineCompare.loop (tape 2) (tape 3) (labels .compare)
        (some (labels .equal)) (some (labels .different)))
  | .equal => emit (tape 5) true exit
  | .different => emit (tape 5) false exit

def copySteps (n : Nat) : Nat := 2 * (n + 1) + 1
def compareSteps (a b : Nat) : Nat := max (a + 1) (b + 1) + 1
def steps (a b : Nat) : Nat := copySteps a + copySteps b + compareSteps a b + 1

theorem steps_le (a b : Nat) : steps a b ≤ 3 * (a + b) + 9 := by
  unfold steps copySteps compareSteps
  omega

theorem encodeWord_eq_iff (a b : Nat) : encodeWord a = encodeWord b ↔ a = b := by
  constructor
  · intro h
    have hlength := congrArg List.length h
    simp only [encodeWord_length] at hlength
    omega
  · rintro rfl
    rfl

theorem emit_step (destination : K) (bit : Bool) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (label : Λ) (atEmit : program label = emit destination bit exit)
    (state : State A) (base : K → List Bool) :
    TM2.step program ⟨some label, state, base⟩ =
      some ⟨exit, state,
        Function.update base destination (bitEncoding bit ++ base destination)⟩ := by
  change some (TM2.stepAux (program label) state base) = _
  rw [atEmit]
  cases bit <;> cases exit <;>
    simp [emit, exitAt, TM2.stepAux, bitEncoding, encodeWord, Function.update_idem]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem equalityTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (tape 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (tape 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (tape 2) = []) (rightEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (ambient : A) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .seedLeft), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update base (tape 5) (bitEncoding (decide (a = b)) ++ base (tape 5))⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j :=
    fun h => hne (distinct h)
  let midLeft := Function.update base (tape 2) (encodeWord a)
  let midBoth := Function.update midLeft (tape 3) (encodeWord b)
  have leftRun : (advance (TM2.step program))^[copySteps a]
      (some ⟨some (labels .seedLeft), clean ambient, base⟩) =
      some ⟨some (labels .seedRight), clean ambient, midLeft⟩ := by
    simpa only [copySteps, clean, midLeft, Nat.one_mul, Nat.add_zero,
      leftEmpty, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 0) (tape 4) (tape 2)
        (hd 0 4 (by decide)) (hd 0 2 (by decide)) (hd 4 2 (by decide)) 1 0
        (labels .seedLeft) (labels .scanLeft) (labels .restoreLeft)
        (some (labels .seedRight)) program (atLabels .seedLeft)
        (atLabels .scanLeft) (atLabels .restoreLeft)
        base a leftSuffix leftWord scratchEmpty (ambient, false, none) none
  have rightSource : midLeft (tape 1) = encodeWord b ++ rightSuffix := by
    simpa [midLeft, hd 1 2 (by decide)] using rightWord
  have scratchAfterLeft : midLeft (tape 4) = [] := by
    simpa [midLeft, hd 4 2 (by decide)] using scratchEmpty
  have rightCopyAfterLeft : midLeft (tape 3) = [] := by
    simpa [midLeft, hd 3 2 (by decide)] using rightEmpty
  have rightRun : (advance (TM2.step program))^[copySteps b]
      (some ⟨some (labels .seedRight), clean ambient, midLeft⟩) =
      some ⟨some (labels .compare), clean ambient, midBoth⟩ := by
    simpa only [copySteps, clean, midBoth, Nat.one_mul, Nat.add_zero,
      rightCopyAfterLeft, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 1) (tape 4) (tape 3)
        (hd 1 4 (by decide)) (hd 1 3 (by decide)) (hd 4 3 (by decide)) 1 0
        (labels .seedRight) (labels .scanRight) (labels .restoreRight)
        (some (labels .compare)) program (atLabels .seedRight)
        (atLabels .scanRight) (atLabels .restoreRight)
        midLeft b rightSuffix rightSource scratchAfterLeft (ambient, false, none) none
  have copyLeftWord : midBoth (tape 2) = encodeWord a := by
    simp [midBoth, midLeft, hd 2 3 (by decide)]
  have copyRightWord : midBoth (tape 3) = encodeWord b := by simp [midBoth]
  have restored : Reduction.MachineTransfer.tapesAt (tape 2) (tape 3) midBoth [] [] = base := by
    funext k
    by_cases hl : k = tape 2
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, midBoth, midLeft,
        hd 2 3 (by decide), leftEmpty]
    · by_cases hr : k = tape 3
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, midBoth, midLeft, rightEmpty]
      · simp [Reduction.MachineTransfer.tapesAt, midBoth, midLeft, hl, hr]
  let back := MachineStateEquiv.program (compareStateEquiv A).symm program
  have atCompare : back (labels .compare) =
      MachineCompare.loop (tape 2) (tape 3) (labels .compare)
        (some (labels .equal)) (some (labels .different)) := by
    change MachineStateEquiv.statement (compareStateEquiv A).symm
      (program (labels .compare)) = _
    rw [atLabels .compare]
    exact MachineStateEquiv.statement_symm_statement (compareStateEquiv A) _
  have backForward : MachineStateEquiv.program (compareStateEquiv A) back = program := by
    funext l
    change MachineStateEquiv.statement (compareStateEquiv A)
      (MachineStateEquiv.statement (compareStateEquiv A).symm (program l)) = program l
    simpa only [Equiv.symm_symm] using
      MachineStateEquiv.statement_symm_statement (compareStateEquiv A).symm (program l)
  have compareRun : (advance (TM2.step program))^[compareSteps a b]
      (some ⟨some (labels .compare), clean ambient, midBoth⟩) =
      some ⟨if a = b then some (labels .equal) else some (labels .different),
        clean ambient, base⟩ := by
    have native := MachineCompare.compareTrace_fromTapes (tape 2) (tape 3)
      (hd 2 3 (by decide)) (labels .compare) (some (labels .equal))
      (some (labels .different)) back atCompare midBoth ambient none none
    rw [copyLeftWord, copyRightWord, restored] at native
    simp only [encodeWord_eq_iff, encodeWord_length] at native
    have transported := MachineStateEquiv.trace (compareStateEquiv A) back _ _ _ native
    rw [backForward] at transported
    simpa [MachineStateEquiv.configuration, compareStateEquiv, clean, compareSteps] using
      transported
  have emitRun : TM2.step program
      ⟨if a = b then some (labels .equal) else some (labels .different),
        clean ambient, base⟩ =
      some ⟨exit, clean ambient,
        Function.update base (tape 5) (bitEncoding (decide (a = b)) ++ base (tape 5))⟩ := by
    by_cases heq : a = b
    · simpa only [heq, ite_true, decide_true] using
        emit_step (tape 5) true exit program (labels .equal) (atLabels .equal)
          (clean ambient) base
    · simpa only [heq, ite_false, decide_false] using
        emit_step (tape 5) false exit program (labels .different) (atLabels .different)
          (clean ambient) base
  have copied := joinTrace leftRun rightRun
  have compared := joinTrace copied compareRun
  rw [steps, Function.iterate_succ_apply', compared, advance_some]
  exact emitRun

def equalityInTime (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (tape 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (tape 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (tape 2) = []) (rightEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .seedLeft), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update base (tape 5) (bitEncoding (decide (a = b)) ++ base (tape 5))⟩)
      (3 * (a + b) + 9) where
  steps := steps a b
  evals_in_steps := equalityTrace tape distinct labels exit program atLabels base a b
    leftSuffix rightSuffix leftWord rightWord leftEmpty rightEmpty scratchEmpty ambient
  steps_le_m := steps_le a b

def machine : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 5
  Γ _ := Bool
  Λ := Label
  main := .seedLeft
  σ := State Unit
  initialState := clean ()
  m := instruction id id none

def machineInTime (base : Fin 6 → List Bool) (a b : Nat)
    (leftSuffix rightSuffix : List Bool)
    (leftWord : base 0 = encodeWord a ++ leftSuffix)
    (rightWord : base 1 = encodeWord b ++ rightSuffix)
    (leftEmpty : base 2 = []) (rightEmpty : base 3 = []) (scratchEmpty : base 4 = []) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .seedLeft, clean (), base⟩
      (some ⟨none, clean (),
        Function.update base (5 : Fin 6) (bitEncoding (decide (a = b)) ++ base (5 : Fin 6))⟩)
      (3 * (a + b) + 9) :=
  equalityInTime id (fun _ _ h => h) id none (instruction id id none) (fun _ => rfl)
    base a b leftSuffix rightSuffix leftWord rightWord leftEmpty rightEmpty scratchEmpty ()

end MinUncutGames.Foundations.Complexity.MachineUnaryEqualityBit

end

end OAI
