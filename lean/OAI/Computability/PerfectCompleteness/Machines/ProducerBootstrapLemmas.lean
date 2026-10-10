import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Machines.Runtime
import OAI.Computability.UniqueGames.PCP.SourceMachine

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerBootstrap

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Ports (K : Type) := Fin 5 ↪ K

inductive Label
  | copy | restore | seed
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copy, .restore, .seed]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State (σ : Type) := σ × Option Bool

structure Ready (p : Ports K) (base : K → List Bool) (free : Nat) : Prop where
  source : base (p 0) = encodeWord free
  current : base (p 1) = []
  scratch : base (p 2) = []
  count : base (p 3) = []
  cursor : base (p 4) = []

def copied (p : Ports K) (base : K → List Bool) : K → List Bool :=
  Function.update base (p 1) (base (p 0) ++ base (p 1))

def prepared (p : Ports K) (base : K → List Bool) : K → List Bool :=
  Function.update (Function.update (copied p base) (p 3) (false :: copied p base (p 3)))
    (p 4) (false :: copied p base (p 4))

def statement (p : Ports K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (State σ)
  | .copy => Reduction.MachineTransfer.loopAt (p 0) (p 2) id false
      (labels .copy) (some (labels .restore))
  | .restore => MachineCopy.forkLoop (p 2) (p 0) (p 1) false
      (labels .restore) (some (labels .seed))
  | .seed => .push (p 3) (fun _ => false)
      (.push (p 4) (fun _ => false) (Reduction.MachineTransfer.exitAt (p 4) exit))

theorem prepared_current (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 1) = encodeWord free := by
  simp [prepared, copied, p.injective.eq_iff, ready.source, ready.current]

theorem prepared_source (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 0) = encodeWord free := by
  simp [prepared, copied, p.injective.eq_iff, ready.source]

theorem prepared_count (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 3) = encodeWord 0 := by
  simp [prepared, copied, p.injective.eq_iff, ready.count, encodeWord]

theorem prepared_cursor (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 4) = encodeWord 0 := by
  simp [prepared, copied, p.injective.eq_iff, ready.cursor, encodeWord]

theorem prepared_scratch (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 2) = [] := by
  simp [prepared, copied, p.injective.eq_iff, ready.scratch]

theorem prepared_other (p : Ports K) (base : K → List Bool) (k : K)
    (hc : k ≠ p 1) (ht : k ≠ p 3) (hz : k ≠ p 4) : prepared p base k = base k := by
  simp [prepared, copied, hc, ht, hz]

theorem seedTrace (p : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : program (labels .seed) = statement p labels exit .seed)
    (base : K → List Bool) (ambient : σ) :
    (advance (TM2.step program))^[1]
      (some ⟨some (labels .seed), (ambient, none), copied p base⟩) =
      some ⟨exit, (ambient, none), prepared p base⟩ := by
  change some (TM2.stepAux (program (labels .seed)) _ _) = _
  rw [code]
  cases exit <;>
    simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt, prepared,
      p.injective.eq_iff]

theorem trace (p : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, program (labels l) = statement p labels exit l)
    (base : K → List Bool) (free : Nat) (ready : Ready p base free)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * free + 5]
      (some ⟨some (labels .copy), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), prepared p base⟩ := by
  have hc := MachineCopy.copyTrace (p 0) (p 1) (p 2)
    (p.injective.ne (by decide : (0 : Fin 5) ≠ 1))
    (p.injective.ne (by decide : (0 : Fin 5) ≠ 2))
    (p.injective.ne (by decide : (1 : Fin 5) ≠ 2))
    false (labels .copy) (labels .restore) (some (labels .seed))
    program (code .copy) (code .restore) base ready.scratch ambient register
  have hs := seedTrace p labels exit program (code .seed) base ambient
  have time : 2 * free + 5 = 1 + 2 * ((base (p 0)).length + 1) := by
    rw [ready.source, encodeWord_length]
    omega
  rw [time, Function.iterate_add_apply, hc]
  exact hs

def inTime (p : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, program (labels l) = statement p labels exit l)
    (base : K → List Bool) (free : Nat) (ready : Ready p base free)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copy), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), prepared p base⟩) (2 * free + 5) where
  steps := 2 * free + 5
  evals_in_steps := by
    change (advance (TM2.step program))^[2 * free + 5] _ = _
    exact trace p labels exit program code base free ready ambient register
  steps_le_m := le_rfl

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerBootstrap



namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.RootRefresh


open Turing MachineComposition
open UniqueGamesTheorem.Foundations.Hastad

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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.RootRefresh



namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.StackEncoding

variable {Γ : Type*}

abbrev Cells (Γ : Type*) (S : Nat) := Fin S → Option Γ

def encode (S : Nat) (xs : List Γ) : Cells Γ S := fun i => xs[i.val]?

def read {S : Nat} (cells : Cells Γ S) (n : Nat) : Option Γ :=
  if h : n < S then cells ⟨n, h⟩ else none

def head {S : Nat} (cells : Cells Γ S) : Option Γ := read cells 0

def isEmpty {S : Nat} (cells : Cells Γ S) : Bool := (head cells).isNone

def popShift {S : Nat} (cells : Cells Γ S) : Cells Γ S :=
  fun i => read cells (i.val + 1)

def pushShift {S : Nat} (a : Γ) (cells : Cells Γ S) : Cells Γ S :=
  fun i => if h : i.val = 0 then some a else cells ⟨i.val - 1, by omega⟩

@[simp] theorem encode_apply (S : Nat) (xs : List Γ) (i : Fin S) :
    encode S xs i = xs[i.val]? := rfl

@[simp] theorem encode_nil (S : Nat) : encode S ([] : List Γ) = fun _ => none := by
  funext i
  simp [encode]

@[simp] theorem read_at {S : Nat} (cells : Cells Γ S) (i : Fin S) :
    read cells i.val = cells i := by
  simp [read, i.isLt]

theorem read_of_capacity_le {S : Nat} (cells : Cells Γ S) (n : Nat) (h : S ≤ n) :
    read cells n = none := by
  simp [read, Nat.not_lt.mpr h]

theorem read_encode {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) (n : Nat) :
    read (encode S xs) n = xs[n]? := by
  by_cases hn : n < S
  · simp [read, encode, hn]
  · have hx : xs.length ≤ n := by omega
    simp [read, hn, List.getElem?_eq_none hx]

theorem head_encode {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    head (encode S xs) = xs.head? := by
  rw [head, read_encode xs hlen, List.head?_eq_getElem?]

theorem head_encode_eq_none_iff {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    head (encode S xs) = none ↔ xs = [] := by
  rw [head_encode xs hlen, List.head?_eq_none_iff]

theorem isEmpty_encode {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    isEmpty (encode S xs) = xs.isEmpty := by
  rw [isEmpty, head_encode xs hlen]
  cases xs <;> rfl

theorem isEmpty_encode_eq_true_iff {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    isEmpty (encode S xs) = true ↔ xs = [] := by
  rw [isEmpty_encode xs hlen]
  cases xs <;> simp

theorem encode_tail {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    encode S xs.tail = popShift (encode S xs) := by
  funext i
  change xs.tail[i.val]? = read (encode S xs) (i.val + 1)
  rw [read_encode xs hlen, List.getElem?_tail]

theorem encode_cons {S : Nat} (a : Γ) (xs : List Γ) :
    encode S (a :: xs) = pushShift a (encode S xs) := by
  funext i
  by_cases hi : i.val = 0 <;> simp [encode, pushShift, List.getElem?_cons, hi]

theorem tail_length_le {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    xs.tail.length ≤ S := by
  have ht : xs.tail.length ≤ xs.length := by simp
  omega

theorem cons_length_le {S : Nat} (a : Γ) (xs : List Γ) (hroom : xs.length < S) :
    (a :: xs).length ≤ S := by
  simp only [List.length_cons]
  omega

theorem encode_injective {S : Nat} {xs ys : List Γ}
    (hx : xs.length ≤ S) (hy : ys.length ≤ S)
    (h : encode S xs = encode S ys) : xs = ys := by
  apply List.ext_getElem?
  intro n
  rw [← read_encode xs hx n, ← read_encode ys hy n, h]

theorem encode_eq_iff {S : Nat} {xs ys : List Γ}
    (hx : xs.length ≤ S) (hy : ys.length ≤ S) :
    encode S xs = encode S ys ↔ xs = ys :=
  ⟨encode_injective hx hy, fun h => congrArg (encode S) h⟩

abbrev BoundedStack (Γ : Type*) (S : Nat) := {xs : List Γ // xs.length ≤ S}

def boundedEncoding (S : Nat) : BoundedStack Γ S ↪ Cells Γ S where
  toFun xs := encode S xs.val
  inj' := by
    intro xs ys h
    apply Subtype.ext
    exact encode_injective xs.property ys.property h

def boundedPop {S : Nat} (xs : BoundedStack Γ S) : BoundedStack Γ S :=
  ⟨xs.val.tail, tail_length_le xs.val xs.property⟩

def boundedPush {S : Nat} (a : Γ) (xs : BoundedStack Γ S)
    (hroom : xs.val.length < S) : BoundedStack Γ S :=
  ⟨a :: xs.val, cons_length_le a xs.val hroom⟩

theorem boundedPop_correct {S : Nat} (xs : BoundedStack Γ S) :
    boundedEncoding S (boundedPop xs) = popShift (boundedEncoding S xs) :=
  encode_tail xs.val xs.property

theorem boundedPush_correct {S : Nat} (a : Γ) (xs : BoundedStack Γ S)
    (hroom : xs.val.length < S) :
    boundedEncoding S (boundedPush a xs hroom) = pushShift a (boundedEncoding S xs) :=
  encode_cons a xs.val

section Tapes

variable {K : Type} {Alphabet : K → Type} [DecidableEq K]

def encodeTapes (S : Nat) (tapes : ∀ k, List (Alphabet k)) :
    ∀ k, Cells (Alphabet k) S := fun k => encode S (tapes k)

theorem encodeTapes_update (S : Nat) (tapes : ∀ k, List (Alphabet k))
    (k : K) (replacement : List (Alphabet k)) :
    encodeTapes S (Function.update tapes k replacement) =
      Function.update (encodeTapes S tapes) k (encode S replacement) := by
  funext j
  by_cases h : j = k
  · subst j; simp [encodeTapes]
  · simp [encodeTapes, h]

theorem encodeTapes_pop {S : Nat} (tapes : ∀ k, List (Alphabet k)) (k : K)
    (hlen : (tapes k).length ≤ S) :
    encodeTapes S (Function.update tapes k (tapes k).tail) =
      Function.update (encodeTapes S tapes) k (popShift (encode S (tapes k))) := by
  rw [encodeTapes_update, encode_tail (tapes k) hlen]

theorem encodeTapes_push (S : Nat) (tapes : ∀ k, List (Alphabet k)) (k : K)
    (a : Alphabet k) :
    encodeTapes S (Function.update tapes k (a :: tapes k)) =
      Function.update (encodeTapes S tapes) k (pushShift a (encode S (tapes k))) := by
  rw [encodeTapes_update, encode_cons]

omit [DecidableEq K] in
theorem encodeTapes_injective {S : Nat} {tapes other : ∀ k, List (Alphabet k)}
    (h : ∀ k, (tapes k).length ≤ S) (ho : ∀ k, (other k).length ≤ S)
    (heq : encodeTapes S tapes = encodeTapes S other) : tapes = other := by
  funext k
  exact encode_injective (h k) (ho k) (congrFun heq k)

end Tapes

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.StackEncoding

end OAI
