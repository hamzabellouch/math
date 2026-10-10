import OAI.Computability.BinPacking.Computation.MachineVertexPadding
import OAI.Computability.BinPacking.CookLevin.VerifierCircuit
import OAI.Computability.BinPacking.Information.SourceNonempty

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.InputFrame

open Turing MachineComposition
open BinPackingGames.Reduction.MachineTransfer

abbrev Tape := Fin 3
abbrev Label := Fin 5
abbrev State := Unit × Option Bool
abbrev Alphabet (_ : Tape) := Bool

def scan : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun s head => (s.1, head))
    (.branch (fun s => s.2.isSome)
      (.push 1 (fun s => s.2.getD false)
        (.push 2 (fun _ => true) (.goto fun _ => 1)))
      (.goto fun _ => 2))

def program (label : Label) : TM2.Stmt Alphabet Label State :=
  if label = 0 then .push 2 (fun _ => false) (.goto fun _ => 1)
  else if label = 1 then scan
  else if label = 2 then loopAt 1 0 id false 2 (some 3)
  else if label = 3 then loopAt 2 1 id false 3 (some 4)
  else loopAt 1 0 id false 4 none

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := 0
  σ := State
  initialState := ((), none)
  m := program

def tapes (input saved counter : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then saved else counter

def cfg (label : Option Label) (input saved counter : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input saved counter⟩

@[simp] private theorem tapes_zero (input saved counter : List Bool) :
    tapes input saved counter 0 = input := rfl

@[simp] private theorem tapes_one (input saved counter : List Bool) :
    tapes input saved counter 1 = saved := rfl

@[simp] private theorem tapes_two (input saved counter : List Bool) :
    tapes input saved counter 2 = counter := rfl

private theorem update_zero (input saved counter replacement : List Bool) :
    Function.update (tapes input saved counter) 0 replacement =
      tapes replacement saved counter := by
  funext k
  fin_cases k <;> simp [tapes]

private theorem update_one (input saved counter replacement : List Bool) :
    Function.update (tapes input saved counter) 1 replacement =
      tapes input replacement counter := by
  funext k
  fin_cases k <;> simp [tapes]

private theorem update_two (input saved counter replacement : List Bool) :
    Function.update (tapes input saved counter) 2 replacement =
      tapes input saved replacement := by
  funext k
  fin_cases k <;> simp [tapes]

theorem scanStep_nil (saved counter : List Bool) (register : Option Bool) :
    machine.step (cfg (some 1) [] saved counter register) =
      some (cfg (some 2) [] saved counter) := by
  change some (TM2.stepAux (program 1) _ _) = _
  simp [program, scan, cfg, TM2.stepAux, tapes, update_zero]
  rfl

theorem scanStep_cons (bit : Bool) (input saved counter : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some 1) (bit :: input) saved counter register) =
      some (cfg (some 1) input (bit :: saved) (true :: counter) (some bit)) := by
  change some (TM2.stepAux (program 1) _ _) = _
  simp [program, scan, cfg, TM2.stepAux, tapes, update_zero, update_one, update_two]
  rfl

theorem scanTrace (input saved counter : List Bool) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some 1) input saved counter register)) =
        some (cfg (some 2) [] (input.reverse ++ saved)
          (List.replicate input.length true ++ counter)) := by
  induction input generalizing saved counter register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
      List.reverse_nil, List.replicate_zero, List.nil_append] using
      scanStep_nil saved counter register
  | cons bit input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [advance_some]
    rw [scanStep_cons, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [List.replicate_succ']
    simp only [List.append_assoc, List.singleton_append]

theorem startStep (input : List Bool) :
    machine.step (initList machine input) = some (cfg (some 1) input [] [false]) := by
  change some (TM2.stepAux (program 0) ((),none) _) = _
  simp [program, TM2.stepAux, cfg]
  apply congrArg (fun contents => some (⟨some 1, ((), none), contents⟩ : machine.Cfg))
  funext k
  fin_cases k <;> simp [tapes]

theorem restoreTrace (input : List Bool) (n : Nat) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some 2) [] input.reverse (encodeWord n))) =
        some (cfg (some 3) input [] (encodeWord n)) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 1 0 (by decide)
    id false 2 (some 3) program (by simp [program])
    (tapes [] input.reverse (encodeWord n)) () none
  have ht : tapesAt 1 0 (tapes [] input.reverse (encodeWord n)) [] input =
      tapes input [] (encodeWord n) := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 0 program)^[input.length + 1]
    (some (cfg (some 2) [] input.reverse (encodeWord n))) = _
  simpa only [tapes_one, tapes_zero, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, List.append_nil, ht, nextAt, advance, cfg] using! h

theorem reverseCounterTrace (input : List Bool) (n : Nat) :
    (advance machine.step)^[n + 2]
      (some (cfg (some 3) input [] (encodeWord n))) =
        some (cfg (some 4) input (encodeWord n).reverse []) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 2 1 (by decide)
    id false 3 (some 4) program (by simp [program])
    (tapes input [] (encodeWord n)) () none
  have ht : tapesAt 2 1 (tapes input [] (encodeWord n)) [] (encodeWord n).reverse =
      tapes input (encodeWord n).reverse [] := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 1 program)^[n + 2]
    (some (cfg (some 3) input [] (encodeWord n))) = _
  simpa only [tapes_two, tapes_one, List.map_id_fun, id_eq, List.append_nil,
    encodeWord_length, Nat.add_assoc, ht, nextAt, advance, cfg] using! h

theorem prependTrace (input : List Bool) (n : Nat) :
    (advance machine.step)^[n + 2]
      (some (cfg (some 4) input (encodeWord n).reverse [])) =
        some (cfg none (encodeWord n ++ input) [] []) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 1 0 (by decide)
    id false 4 none program (by simp [program])
    (tapes input (encodeWord n).reverse []) () none
  have ht : tapesAt 1 0 (tapes input (encodeWord n).reverse []) [] (encodeWord n ++ input) =
      tapes (encodeWord n ++ input) [] [] := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 0 program)^[n + 2]
    (some (cfg (some 4) input (encodeWord n).reverse [])) = _
  simpa only [tapes_one, tapes_zero, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, encodeWord_length, Nat.add_assoc, ht, nextAt, advance, cfg] using! h

theorem stopped_eq_haltList (output : List Bool) :
    cfg none output [] [] = haltList machine output := by
  unfold cfg haltList
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem frameTrace (input : List Bool) :
    (advance machine.step)^[4 * input.length + 7]
      (some (initList machine input)) =
        some (haltList machine (encodeWord input.length ++ input)) := by
  have join :
      (advance machine.step)^[input.length + 2]
        ((advance machine.step)^[input.length + 2]
          ((advance machine.step)^[input.length + 1]
            ((advance machine.step)^[input.length + 1]
              ((advance machine.step)^[1] (some (initList machine input)))))) =
        (advance machine.step)^[4 * input.length + 7]
          (some (initList machine input)) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      ← Function.iterate_add_apply, ← Function.iterate_add_apply]
    congr 1
    omega
  rw [← join]
  simp only [Function.iterate_one, advance_some]
  rw [startStep, scanTrace]
  simp only [List.append_nil]
  change (advance machine.step)^[input.length + 2]
    ((advance machine.step)^[input.length + 2]
      ((advance machine.step)^[input.length + 1]
        (some (cfg (some 2) [] input.reverse (encodeWord input.length))))) = _
  rw [restoreTrace, reverseCounterTrace, prependTrace, stopped_eq_haltList]

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id
      (fun input => encodeWord input.length ++ input) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 4 * Polynomial.X + 7
  outputsFun input := {
    steps := 4 * input.length + 7
    evals_in_steps := by
      change (advance machine.step)^[4 * input.length + 7]
        (some (initList machine (input.map id))) =
          some (haltList machine ((encodeWord input.length ++ input).map id))
      simp only [List.map_id_fun, id_eq]
      exact frameTrace input
    steps_le_m := by simp }

end BinPackingGames.Foundations.Complexity.CookLevin.InputFrame

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation

open Turing MachineComposition
open BinPackingGames.Foundations.Hastad.SourceHeaderCounts
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
    | inl a => cases b <;> cases h; rfl
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj h))

variable {K Λ σ : Type}

def headSlots {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : MachineHorner.Layout (width p) ↪ K :=
  (headLayout p ps).trans slots

def tailSlots {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : Layout ps ↪ K :=
  (tailLayout p ps).trans slots

@[simp] theorem headSlots_input {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : headSlots slots (.inl 0) = slots (.inl ()) := by
  simp only [headSlots, headLayout, controlSlots]
  rfl

@[simp] theorem headSlots_output {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) :
    headSlots slots (.inl 3) = slots (.inr (.inl (.inl 2))) := rfl

@[simp] theorem tailSlots_input {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : tailSlots slots (.inl ()) = slots (.inl ()) := by
  simp only [tailSlots]
  rfl

theorem head_output_ne_tail {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) (i : Layout ps) :
    headSlots slots (.inl 3) ≠ tailSlots slots i := by
  change slots (.inr (.inl (.inl 2))) ≠ slots (tailLayout p ps i)
  apply slots.injective.ne
  cases i <;> intro h <;> cases h

def Clean (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K) (base : K → List Bool) : Prop :=
  ∀ i : Private ps, base (slots (.inr i)) = []

theorem head_clean {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) (base : K → List Bool) (h : Clean (p :: ps) slots base) :
    MachineHorner.Clean (headSlots slots) base :=
  ⟨h (.inl (.inl 0)), h (.inl (.inl 1)), h (.inl (.inl 3)), h (.inl (.inl 4))⟩

theorem head_coefficients_clean {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) (base : K → List Bool) (h : Clean (p :: ps) slots base)
    (i : Fin (width p)) : base (headSlots slots (.inr i)) = [] :=
  h (.inl (.inr i))

variable [DecidableEq K]

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

end BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierFront
open Turing MachineComposition
open BinPackingGames.Foundations.Hastad

abbrev Tape (V : NPVerifier) := Fin 3 ⊕ ClockPreparation.Layout (ClockPreparation.clockPolynomials V)
abbrev ExtraLabel (V : NPVerifier) := Fin 4 ⊕ ClockPreparation.ProgramLabel (ClockPreparation.clockPolynomials V)
abbrev Label (V : NPVerifier) := InputFrame.Label ⊕ ExtraLabel V
abbrev State (A : Type) := A × Option Bool
abbrev EmbeddedAlphabet (V : NPVerifier) := MachineEmbedding.Alphabet InputFrame.Alphabet
  (fun _ : ClockPreparation.Layout (ClockPreparation.clockPolynomials V) => Bool)

def raw (V : NPVerifier) : Tape V := .inl 0
def stream (V : NPVerifier) : Tape V := .inl 1
def scratch (V : NPVerifier) : Tape V := .inl 2
def clockSlots (V : NPVerifier) : ClockPreparation.Layout (ClockPreparation.clockPolynomials V) ↪ Tape V :=
  ⟨Sum.inr, Sum.inr_injective⟩
def lengthTape (V : NPVerifier) : Tape V := clockSlots V (.inl ())
def clockTape (V : NPVerifier) (c : ClockPreparation.Clock) : Tape V :=
  clockSlots V (ClockPreparation.outputSlot _ (ClockPreparation.clockOutput V c))
def phase (V : NPVerifier) (i : Fin 4) : Label V := .inr (.inl i)
def clockLabel (V : NPVerifier) (l : ClockPreparation.ProgramLabel (ClockPreparation.clockPolynomials V)) : Label V :=
  .inr (.inr l)

def frameStates (A : Type) : (InputFrame.State × A) ≃ State A where
  toFun s := (s.2, s.1.2)
  invFun s := (((), s.2), s.1)
  left_inv := by rintro ⟨⟨⟨⟩, r⟩, a⟩; rfl
  right_inv _ := rfl

def clockStates (A : Type) : MachineHorner.State A ≃ State A where
  toFun s := (s.1.1, s.2)
  invFun s := ((s.1, ()), s.2)
  left_inv := by rintro ⟨⟨a, ⟨⟩⟩, r⟩; rfl
  right_inv _ := rfl

theorem alphabet_eq (V : NPVerifier) : EmbeddedAlphabet V = (fun _ : Tape V => Bool) := by
  funext k
  cases k <;> rfl

variable {A : Type}

def extraProgram (V : NPVerifier) : ExtraLabel V → TM2.Stmt (fun _ : Tape V => Bool) (Label V) (State A)
  | .inl i => if i = 0 then
      Reduction.MachineTransfer.loopAt (raw V) (scratch V) id false (phase V 0) (some (phase V 1))
    else if i = 1 then
      MachineCopy.forkLoop (scratch V) (raw V) (stream V) false (phase V 1) (some (phase V 2))
    else if i = 2 then SourceMachine.fieldStart (lengthTape V) (phase V 3)
    else SourceMachine.fieldLoop (raw V) (lengthTape V) (phase V 3) (some (clockLabel V (.inl ())))
  | .inr l => MachineSubroutine.statement (clockLabel V) none
      (MachineStateEquiv.statement (clockStates A)
        (ClockPreparation.program (ClockPreparation.clockPolynomials V) (clockSlots V) l))

def innerExtra (V : NPVerifier) : ExtraLabel V →
    TM2.Stmt (EmbeddedAlphabet V) (Label V) (InputFrame.State × A) := fun l =>
  MachineStateEquiv.statement (frameStates A).symm
    (MachineAlphabetTransport.statement (alphabet_eq V).symm (extraProgram V l))

def embeddedProgram (V : NPVerifier) : Label V →
    TM2.Stmt (EmbeddedAlphabet V) (Label V) (InputFrame.State × A) :=
  MachineEmbedding.program (some (phase V 0)) InputFrame.program (innerExtra V)

def program (V : NPVerifier) : Label V → TM2.Stmt (fun _ : Tape V => Bool) (Label V) (State A) :=
  MachineAlphabetTransport.program (alphabet_eq V)
    (MachineStateEquiv.program (frameStates A) (embeddedProgram V))

@[simp] theorem program_extra (V : NPVerifier) (l : ExtraLabel V) :
    program (A := A) V (.inr l) = extraProgram V l := by
  simp only [program, MachineAlphabetTransport.program, MachineStateEquiv.program,
    embeddedProgram, MachineEmbedding.program, innerExtra]
  have h := MachineStateEquiv.statement_symm_statement (frameStates A).symm
    (MachineAlphabetTransport.statement (alphabet_eq V).symm (extraProgram (A := A) V l))
  simp only [Equiv.symm_symm] at h
  rw [h]
  exact MachineAlphabetTransport.statement_roundtrip _ _

def frameTapes (V : NPVerifier) (word : List Bool) : Tape V → List Bool
  | .inl i => if i = 0 then word else []
  | .inr _ => []

def framedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  frameTapes V (encodeWord input.length ++ input)

def copiedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  Function.update (framedTapes V input) (stream V) (encodeWord input.length ++ input)

def seedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  Function.update (Function.update (copiedTapes V input) (raw V) input)
    (lengthTape V) (encodeWord input.length)

def preparedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  ClockPreparation.resultTapes (ClockPreparation.clockPolynomials V) (clockSlots V)
    (seedTapes V input) input.length

private theorem alphabet_tapes_apply {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : ∀ k, List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem uniform_frame_tapes (V : NPVerifier) (word : List Bool) :
    MachineAlphabetTransport.tapes (alphabet_eq V)
      (MachineEmbedding.tapes (InputFrame.tapes word [] []) (fun _ => [])) = frameTapes V word := by
  funext k
  rw [alphabet_tapes_apply]
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr k => rfl

def frameInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (.inl 0), (ambient, none), frameTapes V input⟩
      (some ⟨some (phase V 0), (ambient, none), framedTapes V input⟩)
      (4 * input.length + 7) := by
  have hi : initList InputFrame.machine input = InputFrame.cfg (some 0) input [] [] := by
    unfold initList InputFrame.cfg
    congr 1
    funext i
    fin_cases i <;> simp [InputFrame.machine, InputFrame.tapes]
  let original : StateTransition.EvalsToInTime (TM2.step InputFrame.program)
      (InputFrame.cfg (some 0) input [] [])
      (some (InputFrame.cfg none (encodeWord input.length ++ input) [] []))
      (4 * input.length + 7) := {
    steps := 4 * input.length + 7
    evals_in_steps := by
      rw [← hi, InputFrame.stopped_eq_haltList]
      exact InputFrame.frameTrace input
    steps_le_m := le_rfl }
  have em := embeddedExecution (some (phase V 0)) ambient (fun _ => [])
    InputFrame.program (innerExtra V) original
  have st := MachineStateEquiv.execution (frameStates A) (embeddedProgram V) em
  have result := MachineAlphabetTransport.executionInTime (alphabet_eq V)
    (MachineStateEquiv.program (frameStates A) (embeddedProgram V)) st
  simpa only [program, InputFrame.cfg, MachineAlphabetTransport.configuration_mk,
    MachineStateEquiv.configuration, MachineEmbedding.configuration, MachineEmbedding.label,
    Option.map_some, frameStates, Equiv.coe_fn_mk, uniform_frame_tapes, framedTapes] using result

def copyInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (phase V 0), (ambient, none), framedTapes V input⟩
      (some ⟨some (phase V 2), (ambient, none), copiedTapes V input⟩)
      (4 * input.length + 4) := by
  have run := MachineCopy.copyInTime (raw V) (stream V) (scratch V)
    (by simp [raw, stream]) (by simp [raw, scratch]) (by simp [stream, scratch])
    false (phase V 0) (phase V 1) (some (phase V 2)) (program V)
    (by simp [phase, extraProgram]) (by simp [phase, extraProgram])
    (framedTapes V input) (by simp [framedTapes, frameTapes, scratch]) ambient none
  have hb : 2 * ((framedTapes V input (raw V)).length + 1) = 4 * input.length + 4 := by
    simp only [framedTapes, frameTapes, raw, ite_true, List.length_append, encodeWord_length]
    omega
  rw [hb] at run
  simpa [framedTapes, frameTapes, raw, stream, copiedTapes] using run

def fieldInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (phase V 2), (ambient, none), copiedTapes V input⟩
      (some ⟨some (clockLabel V (.inl ())), (ambient, none), seedTapes V input⟩)
      (input.length + 2) := by
  have run := SourceMachine.fieldInTime (raw V) (lengthTape V)
    (by simp [raw, lengthTape, clockSlots]) (phase V 2) (phase V 3)
    (some (clockLabel V (.inl ()))) (program V)
    (by simp [phase, extraProgram]) (by simp [phase, extraProgram])
    (copiedTapes V input) input.length input
    (by simp [copiedTapes, raw, stream, framedTapes, frameTapes]) ambient none
  simpa [SourceMachine.fieldTapes, seedTapes, copiedTapes, lengthTape, clockSlots,
    stream, framedTapes, frameTapes] using run

theorem seed_input (V : NPVerifier) (input : List Bool) :
    seedTapes V input (clockSlots V (.inl ())) = encodeWord input.length := by
  simp [seedTapes, lengthTape]

theorem seed_clean (V : NPVerifier) (input : List Bool) :
    ClockPreparation.Clean (ClockPreparation.clockPolynomials V) (clockSlots V) (seedTapes V input) := by
  intro i
  simp [seedTapes, copiedTapes, framedTapes, frameTapes, lengthTape, raw, stream, clockSlots]

def clocksInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (clockLabel V (.inl ())), (ambient, none), seedTapes V input⟩
      (some ⟨none, (ambient, none), preparedTapes V input⟩)
      ((1 + ClockPreparation.timePolynomial (ClockPreparation.clockPolynomials V)).eval input.length) := by
  have original := ClockPreparation.clocksInTime V (clockSlots V) (seedTapes V input)
    input.length (seed_input V input) (seed_clean V input) ambient none
  have st := MachineStateEquiv.execution (clockStates A)
    (ClockPreparation.program (ClockPreparation.clockPolynomials V) (clockSlots V)) original
  have sub := MachineSubroutine.execution (clockLabel V) none
    (MachineStateEquiv.program (clockStates A)
      (ClockPreparation.program (ClockPreparation.clockPolynomials V) (clockSlots V)))
    (program V) (by intro l; simp [clockLabel, extraProgram, MachineStateEquiv.program]) st
  simpa only [MachineSubroutine.configuration, MachineSubroutine.label,
    MachineStateEquiv.configuration, Option.map_some, clockStates, Equiv.coe_fn_mk,
    preparedTapes] using sub

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  Polynomial.C 9 * Polynomial.X + Polynomial.C 14 + ClockPreparation.timePolynomial (ClockPreparation.clockPolynomials V)

def prepareInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (.inl 0), (ambient, none), frameTapes V input⟩
      (some ⟨none, (ambient, none), preparedTapes V input⟩)
      ((timePolynomial V).eval input.length) := by
  let one := frameInTime V input ambient
  let two := copyInTime V input ambient
  let three := fieldInTime V input ambient
  let four := clocksInTime V input ambient
  let a := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ one two
  let b := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ a three
  let c := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ b four
  exact {
    toEvalsTo := c.toEvalsTo
    steps_le_m := by
      have h := c.steps_le_m
      simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one] at *
      omega }

def callerInTime {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ)
    (caller : Λ → TM2.Stmt (fun _ : Tape V => Bool) Λ (State A))
    (atLabels : ∀ l, caller (labels l) = MachineSubroutine.statement labels exit (program V l))
    (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step caller)
      ⟨some (labels (.inl 0)), (ambient, none), frameTapes V input⟩
      (some ⟨exit, (ambient, none), preparedTapes V input⟩)
      ((timePolynomial V).eval input.length) := by
  exact MachineSubroutine.execution labels exit (program V) caller atLabels
    (prepareInTime V input ambient)

theorem prepared_raw (V : NPVerifier) (input : List Bool) :
    preparedTapes V input (raw V) = input := by
  rw [preparedTapes, ClockPreparation.resultTapes_ambient]
  · simp [seedTapes, lengthTape, clockSlots, raw]
  · rintro ⟨i, hi⟩
    cases hi

theorem prepared_stream (V : NPVerifier) (input : List Bool) :
    preparedTapes V input (stream V) = encodeWord input.length ++ input := by
  rw [preparedTapes, ClockPreparation.resultTapes_ambient]
  · simp [seedTapes, lengthTape, clockSlots, raw, stream, copiedTapes]
  · rintro ⟨i, hi⟩
    cases hi

theorem prepared_length (V : NPVerifier) (input : List Bool) :
    preparedTapes V input (lengthTape V) = encodeWord input.length := by
  rw [preparedTapes, ClockPreparation.resultTapes_off_outputs]
  · exact seed_input V input
  · intro i h
    exact ClockPreparation.outputSlot_ne_input _ i ((clockSlots V).injective h)

theorem prepared_clock (V : NPVerifier) (input : List Bool) (c : ClockPreparation.Clock) :
    preparedTapes V input (clockTape V c) =
      encodeWord (ClockPreparation.clockValue V input.length c) :=
  ClockPreparation.clockResult_output V (clockSlots V) (seedTapes V input) input.length
    (seed_clean V input) c

theorem clockOutput_surjective (V : NPVerifier) :
    Function.Surjective (ClockPreparation.clockOutput V) := by
  intro i
  rcases i with (⟨⟩ | (⟨⟩ | (⟨⟩ | (⟨⟩ | (⟨⟩ | (⟨⟩ | i))))))
  · exact ⟨.witness, rfl⟩
  · exact ⟨.horizon, rfl⟩
  · exact ⟨.capacity, rfl⟩
  · exact ⟨.width, rfl⟩
  · exact ⟨.frameWidth, rfl⟩
  · exact ⟨.inputCount, rfl⟩
  · exact Empty.elim i

theorem prepared_work_clear (V : NPVerifier) (input : List Bool) (k : Tape V)
    (hr : k ≠ raw V) (hs : k ≠ stream V) (hn : k ≠ lengthTape V)
    (hc : ∀ c, k ≠ clockTape V c) : preparedTapes V input k = [] := by
  rw [preparedTapes, ClockPreparation.resultTapes_off_outputs]
  · simp only [seedTapes, Function.update_of_ne hn, Function.update_of_ne hr,
      copiedTapes, Function.update_of_ne hs, framedTapes]
    cases k with
    | inl i =>
      have hi : i ≠ 0 := by intro h; exact hr (congrArg Sum.inl h)
      simp [frameTapes, hi]
    | inr i => rfl
  · intro i h
    obtain ⟨c, rfl⟩ := clockOutput_surjective V i
    exact hc c h.symm

def machine (V : NPVerifier) : FinTM2 where
  K := Tape V
  k₀ := raw V
  k₁ := stream V
  Γ _ := Bool
  Λ := Label V
  main := .inl 0
  σ := State Unit
  initialState := ((), none)
  m := program V

theorem initial_configuration (V : NPVerifier) (input : List Bool) :
    initList (machine V) input =
      (⟨some (.inl 0), ((), none), frameTapes V input⟩ : (machine V).Cfg) := by
  unfold initList
  congr 1
  funext k
  cases k with
  | inl i => (by_cases hi : i = 0 <;> simp [machine, raw, frameTapes, hi]); rfl
  | inr i => simp [machine, raw, frameTapes]

def machineInTime (V : NPVerifier) (input : List Bool) :
    StateTransition.EvalsToInTime (machine V).step (initList (machine V) input)
      (some ⟨none, ((), none), preparedTapes V input⟩)
      ((timePolynomial V).eval input.length) := by
  rw [initial_configuration]
  exact prepareInTime V input ()

theorem finite_work_alphabets (V : NPVerifier) (k : (machine V).K) :
    Finite ((machine V).Γ k) := by
  change Finite Bool
  infer_instance

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierFront

end

end OAI
