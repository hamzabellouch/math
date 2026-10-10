import OAI.Computability.PerfectCompleteness.Machines.VerifierCircuit
import OAI.Computability.UniqueGames.PCP.SourceHeaderCounts

namespace OAI

section


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ClockPreparation

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts
open PolynomialMachine

abbrev PhasePrivate (p : Polynomial Nat) := Fin 5 ⊕ Fin (width p)

def Private : List (Polynomial Nat) → Type
  | [] => Empty
  | p :: ps => PhasePrivate p ⊕ Private ps

abbrev Layout (ps : List (Polynomial Nat)) := Unit ⊕ Private ps

def Label : List (Polynomial Nat) → Type
  | [] => Empty
  | p :: ps => Eval.Label p ⊕ Label ps

def Output : List (Polynomial Nat) → Type
  | [] => Empty
  | _ :: ps => Unit ⊕ Output ps

instance privateFintype (ps : List (Polynomial Nat)) : Fintype (Private ps) := by
  induction ps with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons p ps ih =>
    letI := ih
    exact inferInstanceAs (Fintype (PhasePrivate p ⊕ Private ps))

instance privateDecidableEq (ps : List (Polynomial Nat)) : DecidableEq (Private ps) := by
  induction ps with
  | nil => exact inferInstanceAs (DecidableEq Empty)
  | cons p ps ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (PhasePrivate p ⊕ Private ps))

instance labelFintype (ps : List (Polynomial Nat)) : Fintype (Label ps) := by
  induction ps with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons p ps ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Eval.Label p ⊕ Label ps))

instance labelDecidableEq (ps : List (Polynomial Nat)) : DecidableEq (Label ps) := by
  induction ps with
  | nil => exact inferInstanceAs (DecidableEq Empty)
  | cons p ps ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Eval.Label p ⊕ Label ps))

instance outputFintype (ps : List (Polynomial Nat)) : Fintype (Output ps) := by
  induction ps with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons p ps ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Unit ⊕ Output ps))

def controlSlots (p : Polynomial Nat) (ps : List (Polynomial Nat)) : Fin 6 ↪ Layout (p :: ps) where
  toFun i := match i.val with
    | 0 => .inl ()
    | 1 => .inr (.inl (.inl 0))
    | 2 => .inr (.inl (.inl 1))
    | 3 => .inr (.inl (.inl 2))
    | 4 => .inr (.inl (.inl 3))
    | _ => .inr (.inl (.inl 4))
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> cases h <;> rfl

def headLayout (p : Polynomial Nat) (ps : List (Polynomial Nat)) :
    MachineHorner.Layout (width p) ↪ Layout (p :: ps) where
  toFun
    | .inl i => controlSlots p ps i
    | .inr i => .inr (.inl (.inr i))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((controlSlots p ps).injective h)
      | inr b => fin_cases a <;> cases h
    | inr a =>
      cases b with
      | inl b => fin_cases b <;> cases h
      | inr b =>
        exact congrArg Sum.inr (Sum.inr.inj (Sum.inl.inj (Sum.inr.inj h)))

def tailLayout (p : Polynomial Nat) (ps : List (Polynomial Nat)) :
    Layout ps ↪ Layout (p :: ps) where
  toFun
    | .inl _ => .inl ()
    | .inr i => .inr (.inr i)
  inj' := by
    intro a b h
    cases a with
    | inl a => (cases b <;> cases h); rfl
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj h))

variable {K Λ σ : Type} [DecidableEq K]

def headSlots {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : MachineHorner.Layout (width p) ↪ K :=
  (headLayout p ps).trans slots

def tailSlots {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : Layout ps ↪ K :=
  (tailLayout p ps).trans slots

omit [DecidableEq K] in
@[simp] theorem headSlots_input {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : headSlots slots (.inl 0) = slots (.inl ()) := rfl

omit [DecidableEq K] in
@[simp] theorem headSlots_output {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) :
    headSlots slots (.inl 3) = slots (.inr (.inl (.inl 2))) := rfl

omit [DecidableEq K] in
@[simp] theorem tailSlots_input {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : tailSlots slots (.inl ()) = slots (.inl ()) := rfl

omit [DecidableEq K] in
theorem head_output_ne_tail {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) (i : Layout ps) :
    headSlots slots (.inl 3) ≠ tailSlots slots i := by
  have controlPort : controlSlots p ps 3 = (.inr (.inl (.inl 2)) : Layout (p :: ps)) := by
    rw [controlSlots.eq_1]
    rfl
  have headPort : headLayout p ps (.inl 3) = (.inr (.inl (.inl 2)) : Layout (p :: ps)) := by
    rw [headLayout.eq_1]
    exact controlPort
  rw [headSlots.eq_1, tailSlots.eq_1]
  change slots (headLayout p ps (.inl 3)) ≠ slots (tailLayout p ps i)
  rw [headPort]
  cases i with
  | inl =>
    change slots (.inr (.inl (.inl 2))) ≠ slots (.inl ())
    exact slots.injective.ne (by intro h; cases h)
  | inr i =>
    change slots (.inr (.inl (.inl 2))) ≠ slots (.inr (.inr i))
    exact slots.injective.ne (by intro h; cases h)

def Clean (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K) (base : K → List Bool) : Prop :=
  ∀ i : Private ps, base (slots (.inr i)) = []

omit [DecidableEq K] in
theorem head_clean {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) (base : K → List Bool) (h : Clean (p :: ps) slots base) :
    MachineHorner.Clean (headSlots slots) base :=
  ⟨h (.inl (.inl 0)), h (.inl (.inl 1)), h (.inl (.inl 3)), h (.inl (.inl 4))⟩

omit [DecidableEq K] in
theorem head_coefficients_clean {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) (base : K → List Bool) (h : Clean (p :: ps) slots base)
    (i : Fin (width p)) : base (headSlots slots (.inr i)) = [] :=
  h (.inl (.inr i))

theorem tail_clean_after_head {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) (base : K → List Bool)
    (h : Clean (p :: ps) slots base) (value : Nat) :
    Clean ps (tailSlots slots) (MachineHorner.resultTapes (headSlots slots) base value) := by
  intro i
  rw [MachineHorner.resultTapes, Function.update_of_ne (head_output_ne_tail slots (.inr i)).symm]
  exact h (.inr i)

def entry : (ps : List (Polynomial Nat)) → (Label ps → Λ) → Option Λ → Option Λ
  | [], _, exit => exit
  | p :: _, labels, _ => some (labels (.inl (Eval.start p)))

def statement : (ps : List (Polynomial Nat)) → (slots : Layout ps ↪ K) →
    (Label ps → Λ) → Option Λ → Label ps →
      TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | [], _, _, _, l => Empty.elim l
  | p :: ps, slots, labels, exit, .inl l =>
      Eval.statement p (headSlots slots) (fun l => labels (.inl l))
        (entry ps (fun l => labels (.inr l)) exit) l
  | _ :: ps, slots, labels, exit, .inr l =>
      statement ps (tailSlots slots) (fun l => labels (.inr l)) exit l

def resultTapes : (ps : List (Polynomial Nat)) → (Layout ps ↪ K) →
    (K → List Bool) → Nat → K → List Bool
  | [], _, base, _ => base
  | p :: ps, slots, base, n =>
      resultTapes ps (tailSlots slots)
        (MachineHorner.resultTapes (headSlots slots) base (p.eval n)) n

def steps : List (Polynomial Nat) → Nat → Nat
  | [], _ => 0
  | p :: ps, n => Eval.steps p n + steps ps n

def timePolynomial : List (Polynomial Nat) → Polynomial Nat
  | [] => 0
  | p :: ps => PolynomialMachine.timePolynomial p + timePolynomial ps

theorem steps_le_timePolynomial (ps : List (Polynomial Nat)) (n : Nat) :
    steps ps n ≤ (timePolynomial ps).eval n := by
  induction ps with
  | nil => simp [steps, timePolynomial]
  | cons p ps ih =>
    have hp : Eval.steps p n ≤ (PolynomialMachine.timePolynomial p).eval n := by
      rw [PolynomialMachine.timePolynomial_eval]
      unfold Eval.steps
      omega
    simpa only [steps, timePolynomial, Polynomial.eval_add] using Nat.add_le_add hp ih

private theorem trace_trans {A : Type*} (f : A → A) {a b : Nat} {x y z : A}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem trace (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (labels : Label ps → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement ps slots labels exit l)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl ())) = encodeWord n) (clean : Clean ps slots base)
    (ambient : σ) :
    (advance (TM2.step program))^[steps ps n]
      (some ⟨entry ps labels exit, ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes ps slots base n⟩ := by
  induction ps generalizing base with
  | nil => rfl
  | cons p ps ih =>
    have first := Eval.trace p (headSlots slots) (fun l => labels (.inl l))
      (entry ps (fun l => labels (.inr l)) exit) program
      (fun l => atLabels (.inl l)) base n (by simpa using hinput)
      (head_coefficients_clean slots base clean) (head_clean slots base clean) ambient none
    have hnext : MachineHorner.resultTapes (headSlots slots) base (p.eval n)
        (tailSlots slots (.inl ())) = encodeWord n := by
      rw [MachineHorner.resultTapes,
        Function.update_of_ne (head_output_ne_tail slots (.inl ())).symm]
      exact hinput
    have second := ih (tailSlots slots) (fun l => labels (.inr l))
      (fun l => atLabels (.inr l))
      (MachineHorner.resultTapes (headSlots slots) base (p.eval n)) hnext
      (tail_clean_after_head slots base clean (p.eval n))
    exact trace_trans _ first second

def outputSlot : (ps : List (Polynomial Nat)) → Output ps → Layout ps
  | [], i => Empty.elim i
  | _ :: _, .inl _ => .inr (.inl (.inl 2))
  | p :: ps, .inr i => tailLayout p ps (outputSlot ps i)

def outputPolynomial : (ps : List (Polynomial Nat)) → Output ps → Polynomial Nat
  | [], i => Empty.elim i
  | p :: _, .inl _ => p
  | _ :: ps, .inr i => outputPolynomial ps i

theorem outputSlot_private (ps : List (Polynomial Nat)) (i : Output ps) :
    ∃ k : Private ps, outputSlot ps i = .inr k := by
  induction ps with
  | nil => exact Empty.elim i
  | cons p ps ih =>
    cases i with
    | inl i => exact ⟨.inl (.inl 2), rfl⟩
    | inr i =>
      obtain ⟨k, hk⟩ := ih i
      refine ⟨.inr k, ?_⟩
      simp only [outputSlot, hk, tailLayout]
      rfl

theorem outputSlot_ne_input (ps : List (Polynomial Nat)) (i : Output ps) :
    outputSlot ps i ≠ .inl () := by
  obtain ⟨k, hk⟩ := outputSlot_private ps i
  rw [hk]
  intro h
  cases h

theorem outputSlot_injective (ps : List (Polynomial Nat)) :
    Function.Injective (outputSlot ps) := by
  induction ps with
  | nil => intro i; exact Empty.elim i
  | cons p ps ih =>
    intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => cases i; cases j; rfl
      | inr j =>
        exact False.elim ((head_output_ne_tail (Function.Embedding.refl (Layout (p :: ps)))
          (outputSlot ps j)) h)
    | inr i =>
      cases j with
      | inl j =>
        exact False.elim ((head_output_ne_tail (Function.Embedding.refl (Layout (p :: ps)))
          (outputSlot ps i)) h.symm)
      | inr j => exact congrArg Sum.inr (ih ((tailLayout p ps).injective h))

theorem resultTapes_off_outputs (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat) (k : K)
    (hk : ∀ i : Output ps, slots (outputSlot ps i) ≠ k) :
    resultTapes ps slots base n k = base k := by
  induction ps generalizing base with
  | nil => rfl
  | cons p ps ih =>
    change resultTapes ps (tailSlots slots)
      (MachineHorner.resultTapes (headSlots slots) base (p.eval n)) n k = base k
    rw [ih _ _ (fun i => hk (.inr i))]
    exact Function.update_of_ne (hk (.inl ())).symm _ _

theorem resultTapes_input (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat) :
    resultTapes ps slots base n (slots (.inl ())) = base (slots (.inl ())) := by
  apply resultTapes_off_outputs
  intro i hi
  exact outputSlot_ne_input ps i (slots.injective hi)

theorem resultTapes_output (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat) (clean : Clean ps slots base) (i : Output ps) :
    resultTapes ps slots base n (slots (outputSlot ps i)) =
      encodeWord ((outputPolynomial ps i).eval n) := by
  induction ps generalizing base with
  | nil => exact Empty.elim i
  | cons p ps ih =>
    cases i with
    | inl i =>
      change resultTapes ps (tailSlots slots)
        (MachineHorner.resultTapes (headSlots slots) base (p.eval n)) n
          (headSlots slots (.inl 3)) = encodeWord (p.eval n)
      rw [resultTapes_off_outputs _ _ _ _ _
        (fun i => (head_output_ne_tail slots (outputSlot ps i)).symm)]
      rw [MachineHorner.resultTapes_output]
      simp only [headSlots_output, clean (.inl (.inl 2)), List.append_nil]
    | inr i =>
      exact ih (tailSlots slots) _ (tail_clean_after_head slots base clean _) i

theorem resultTapes_work_clear (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat) (clean : Clean ps slots base) (k : Private ps)
    (hk : ∀ i : Output ps, outputSlot ps i ≠ .inr k) :
    resultTapes ps slots base n (slots (.inr k)) = [] := by
  rw [resultTapes_off_outputs _ _ _ _ _ (fun i h => hk i (slots.injective h))]
  exact clean k

theorem resultTapes_ambient (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat) (k : K) (hk : k ∉ Set.range slots) :
    resultTapes ps slots base n k = base k := by
  apply resultTapes_off_outputs
  intro i hi
  exact hk ⟨outputSlot ps i, hi⟩

abbrev ProgramLabel (ps : List (Polynomial Nat)) := Unit ⊕ Label ps

def program (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K) :
    ProgramLabel ps → TM2.Stmt (fun _ : K => Bool) (ProgramLabel ps) (MachineHorner.State σ)
  | .inl _ => .load (fun state => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots (.inl ())) (entry ps Sum.inr none))
  | .inr l => statement ps slots Sum.inr none l

theorem programTrace (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl ())) = encodeWord n) (clean : Clean ps slots base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program ps slots)))^[1 + steps ps n]
      (some ⟨some (.inl ()), ((ambient, ()), register), base⟩) =
      some ⟨none, ((ambient, ()), none), resultTapes ps slots base n⟩ := by
  have first : (advance (TM2.step (program ps slots)))^[1]
      (some ⟨some (.inl ()), ((ambient, ()), register), base⟩) =
      some ⟨entry ps Sum.inr none, ((ambient, ()), none), base⟩ := by
    change some (TM2.stepAux (program ps slots (.inl ())) _ _) = _
    simp only [program, TM2.stepAux]
    cases h : entry ps (Sum.inr : Label ps → ProgramLabel ps) none <;> rfl
  have rest := trace ps slots Sum.inr none (program ps slots) (fun _ => rfl)
    base n hinput clean ambient
  exact trace_trans _ first rest

def programInTime (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl ())) = encodeWord n) (clean : Clean ps slots base)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program ps slots))
      ⟨some (.inl ()), ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), resultTapes ps slots base n⟩)
      ((1 + timePolynomial ps).eval n) where
  steps := 1 + steps ps n
  evals_in_steps := programTrace ps slots base n hinput clean ambient register
  steps_le_m := by
    simp only [Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.add_le_add_left (steps_le_timePolynomial ps n) 1

abbrev Tape (ps : List (Polynomial Nat)) := Layout ps ⊕ Unit

def machineSlots (ps : List (Polynomial Nat)) : Layout ps ↪ Tape ps :=
  ⟨Sum.inl, Sum.inl_injective⟩

def machine (ps : List (Polynomial Nat)) : FinTM2 where
  K := Tape ps
  k₀ := .inr ()
  k₁ := .inr ()
  Γ _ := Bool
  Λ := ProgramLabel ps
  main := .inl ()
  σ := MachineHorner.State Unit
  initialState := (((), ()), none)
  m := program ps (machineSlots ps)

theorem machine_rawInput_preserved (ps : List (Polynomial Nat))
    (base : Tape ps → List Bool) (n : Nat) :
    resultTapes ps (machineSlots ps) base n (.inr ()) = base (.inr ()) := by
  apply resultTapes_ambient
  rintro ⟨i, hi⟩
  cases hi

def machineInTime (ps : List (Polynomial Nat)) (base : Tape ps → List Bool) (n : Nat)
    (hinput : base ((machineSlots ps) (.inl ())) = encodeWord n)
    (clean : Clean ps (machineSlots ps) base) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine ps).step
      ⟨some (.inl ()), (((), ()), register), base⟩
      (some ⟨none, (((), ()), none), resultTapes ps (machineSlots ps) base n⟩)
      ((1 + timePolynomial ps).eval n) :=
  programInTime ps (machineSlots ps) base n hinput clean () register

inductive Clock
  | witness | horizon | capacity | width | frameWidth | inputCount
  deriving DecidableEq

/-- A list enumerating every element of the type, which are all zero-argument constructors. (Generated by the `Fintype` deriving handler.)-/
protected abbrev Clock.enumList : List Clock := [.witness, .horizon, .capacity, .width,
  .frameWidth, .inputCount]

protected theorem Clock.enumList_getElem?_ctorIdx_eq (x : Clock) :
    Clock.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Clock.enumList_nodup : Clock.enumList.Nodup := by decide

instance : Fintype Clock where
  elems := ⟨Clock.enumList, Clock.enumList_nodup⟩
  complete x := by cases x <;> decide

def clockPolynomial (V : NPVerifier) : Clock → Polynomial Nat
  | .witness => V.witnessBound
  | .horizon => Bounds.horizonPolynomial V.computation.time V.witnessBound
  | .capacity => Bounds.capacityPolynomial V.computation.time V.witnessBound
      (Runtime.programPushBound V.computation.tm)
  | .width => VerifierCircuit.widthPolynomial V
  | .frameWidth => VerifierCircuit.widthPolynomial V + 1
  | .inputCount => WitnessEncoding.freeInputPolynomial V.witnessBound

def clockPolynomials (V : NPVerifier) : List (Polynomial Nat) :=
  [clockPolynomial V .witness, clockPolynomial V .horizon, clockPolynomial V .capacity,
    clockPolynomial V .width, clockPolynomial V .frameWidth, clockPolynomial V .inputCount]

def clockOutput (V : NPVerifier) : Clock → Output (clockPolynomials V)
  | .witness => .inl ()
  | .horizon => .inr (.inl ())
  | .capacity => .inr (.inr (.inl ()))
  | .width => .inr (.inr (.inr (.inl ())))
  | .frameWidth => .inr (.inr (.inr (.inr (.inl ()))))
  | .inputCount => .inr (.inr (.inr (.inr (.inr (.inl ())))))

def clockValue (V : NPVerifier) (n : Nat) : Clock → Nat
  | .witness => V.witnessBound.eval n
  | .horizon => V.horizon n
  | .capacity => VerifierCircuit.capacity V n
  | .width => (VerifierCircuit.indexing V).width (VerifierCircuit.capacity V n)
  | .frameWidth => (VerifierCircuit.indexing V).width (VerifierCircuit.capacity V n) + 1
  | .inputCount => 2 * V.witnessBound.eval n + 1

@[simp] theorem outputPolynomial_clockOutput (V : NPVerifier) (c : Clock) :
    outputPolynomial (clockPolynomials V) (clockOutput V c) = clockPolynomial V c := by
  cases c <;> rfl

theorem clockPolynomial_eval (V : NPVerifier) (n : Nat) (c : Clock) :
    (clockPolynomial V c).eval n = clockValue V n c := by
  cases c <;>
    simp [clockPolynomial, clockValue, VerifierCircuit.widthPolynomial,
      VerifierCircuit.capacity, NPVerifier.horizon, ConfigIndex.Indexing.width, Nat.mul_comm]

theorem clockResult_output (V : NPVerifier) (slots : Layout (clockPolynomials V) ↪ K)
    (base : K → List Bool) (n : Nat) (clean : Clean (clockPolynomials V) slots base)
    (c : Clock) :
    resultTapes (clockPolynomials V) slots base n
      (slots (outputSlot (clockPolynomials V) (clockOutput V c))) =
      encodeWord (clockValue V n c) := by
  rw [resultTapes_output _ _ _ _ clean, outputPolynomial_clockOutput, clockPolynomial_eval]

def clocksInTime (V : NPVerifier) (slots : Layout (clockPolynomials V) ↪ K)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl ())) = encodeWord n)
    (clean : Clean (clockPolynomials V) slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (clockPolynomials V) slots))
      ⟨some (.inl ()), ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), resultTapes (clockPolynomials V) slots base n⟩)
      ((1 + timePolynomial (clockPolynomials V)).eval n) :=
  programInTime (clockPolynomials V) slots base n hinput clean ambient register

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ClockPreparation

end

end

end OAI
