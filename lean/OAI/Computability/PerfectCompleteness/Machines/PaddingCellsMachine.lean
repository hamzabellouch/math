import OAI.Computability.PerfectCompleteness.Machines.InitializationControl
import OAI.Computability.PerfectCompleteness.Machines.InputCellsMachineLemmas
import OAI.Computability.PerfectCompleteness.Machines.OrClosure

namespace OAI


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PaddingCellsMachine


open Turing PostfixModel InitializationTemplate VerifierCircuit WitnessEncoding

variable {K Λ σ : Type} [DecidableEq K]

abbrev Ports (K : Type) := Fin 4 ↪ K

def corePorts (p : Ports K) : OrClosure.Ports K where
  remaining := p 3
  reversed := p 1
  count := p 2
  remaining_ne_reversed := fun h => by have := p.injective h; omega
  remaining_ne_count := fun h => by have := p.injective h; omega
  reversed_ne_count := fun h => by have := p.injective h; omega

def literalPorts (p : Ports K) : InitializationControl.Ports K :=
  ⟨p 1, p 2, (corePorts p).reversed_ne_count⟩

abbrev frame (p : Ports K) (base : K → List Bool)
    (remaining output count : List Bool) : K → List Bool :=
  OrClosure.frame (corePorts p) base remaining output count

@[simp] theorem frame_remaining (p : Ports K) (base : K → List Bool)
    (remaining output count : List Bool) :
    frame p base remaining output count (p 3) = remaining := by
  exact OrClosure.frame_remaining (corePorts p) base remaining output count

@[simp] theorem frame_output (p : Ports K) (base : K → List Bool)
    (remaining output count : List Bool) :
    frame p base remaining output count (p 1) = output := by
  exact OrClosure.frame_reversed (corePorts p) base remaining output count

@[simp] theorem frame_count (p : Ports K) (base : K → List Bool)
    (remaining output count : List Bool) :
    frame p base remaining output count (p 2) = count := by
  exact OrClosure.frame_count (corePorts p) base remaining output count

theorem frame_other (p : Ports K) (base : K → List Bool)
    (remaining output count : List Bool) (k : K)
    (hr : k ≠ p 3) (ho : k ≠ p 1) (hc : k ≠ p 2) :
    frame p base remaining output count k = base k :=
  OrClosure.frame_other (corePorts p) base remaining output count k hr ho hc

@[simp] theorem frame_input (p : Ports K) (base : K → List Bool)
    (remaining output count : List Bool) :
    frame p base remaining output count (p 0) = base (p 0) := by
  apply frame_other <;> intro h <;> have := p.injective h <;> omega

@[simp] theorem update_remaining (p : Ports K) (base : K → List Bool)
    (remaining output count replacement : List Bool) :
    Function.update (frame p base remaining output count) (p 3) replacement =
      frame p base replacement output count :=
  OrClosure.update_remaining (corePorts p) base remaining output count replacement

@[simp] theorem literal_emitted (p : Ports K) (base : K → List Bool)
    (remaining output count : List Bool) (row : List Token) :
    InitializationControl.emitted (literalPorts p)
      (frame p base remaining output count) row =
    frame p base remaining ((tokenBits row).reverse ++ output)
      (List.replicate row.length true ++ count) := by
  simp only [InitializationControl.emitted, literalPorts, frame_output, frame_count]
  exact (OrClosure.update_reversed (corePorts p) base remaining output count
      ((tokenBits row).reverse ++ output)).symm ▸
    OrClosure.update_count (corePorts p) base remaining
      ((tokenBits row).reverse ++ output) count (List.replicate row.length true ++ count)

def repeatedRows (row : List Token) (n : Nat) : List Token :=
  (List.replicate n row).flatten

@[simp] theorem repeatedRows_zero (row : List Token) : repeatedRows row 0 = [] := rfl

@[simp] theorem repeatedRows_succ (row : List Token) (n : Nat) :
    repeatedRows row (n + 1) = row ++ repeatedRows row n := by
  simp [repeatedRows, List.replicate_succ]

@[simp] theorem repeatedRows_length (row : List Token) (n : Nat) :
    (repeatedRows row n).length = n * row.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.succ_mul, Nat.add_comm]

def statement (p : Ports K) (row : List Token) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  .pop (p 3) (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.load (fun state => (state.1, none))
        (InitializationControl.literalStatement (literalPorts p) row (some again)))
      (.push (p 3) (fun _ => false)
        (.load (fun state => (state.1, none))
          (InitializationControl.exitStatement exit))))

theorem step_zero (p : Ports K) (row : List Token) (again : Λ) (exit : Option Λ)
    (base : K → List Bool) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (statement p row again exit) (ambient, register)
      (frame p base (encodeWord 0 ++ suffix) output count) =
      ⟨exit, (ambient, none), frame p base (encodeWord 0 ++ suffix) output count⟩ := by
  cases exit <;>
    simp [statement, TM2.stepAux, encodeWord, InitializationControl.exitStatement]

theorem step_succ (p : Ports K) (row : List Token) (again : Λ) (exit : Option Λ)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (statement p row again exit) (ambient, register)
      (frame p base (encodeWord (n + 1) ++ suffix) output count) =
      ⟨some again, (ambient, none), frame p base (encodeWord n ++ suffix)
        ((tokenBits row).reverse ++ output) (List.replicate row.length true ++ count)⟩ := by
  simp [statement, TM2.stepAux, encodeWord, List.replicate_succ,
    InitializationControl.literalStep]

theorem trace (p : Ports K) (row : List Token) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (code : program again = statement p row again exit)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, register),
        frame p base (encodeWord n ++ suffix) output count⟩) =
      some ⟨exit, (ambient, none), frame p base (encodeWord 0 ++ suffix)
        ((tokenBits (repeatedRows row n)).reverse ++ output)
        (List.replicate (n * row.length) true ++ count)⟩ := by
  induction n generalizing output count register with
  | zero =>
      change some (TM2.stepAux (program again) (ambient, register)
        (frame p base (encodeWord 0 ++ suffix) output count)) = _
      rw [code, step_zero]
      simp [tokenBits, tokenWords, encodeWords]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[n + 1]
        (some (TM2.stepAux (program again) (ambient, register)
          (frame p base (encodeWord (n + 1) ++ suffix) output count))) = _
      rw [code, step_succ, ih]
      simp only [repeatedRows_succ, OrClosure.tokenBits_append, List.reverse_append,
        List.append_assoc]
      have hc : List.replicate (n * row.length) true ++
          (List.replicate row.length true ++ count) =
          List.replicate ((n + 1) * row.length) true ++ count := by
        rw [← List.append_assoc, List.replicate_append_replicate, Nat.succ_mul]
      rw [hc]

theorem frame_eq_capacityTapes (p : Ports K) (base : K → List Bool)
    (remaining : Nat) (input output count : List Bool) :
    frame p (Function.update base (p 0) input) (encodeWord remaining) output count =
      InputCellsCapacity.tapes p base remaining input output count := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    fin_cases j <;>
      simp [frame, OrClosure.frame, corePorts, p.injective.eq_iff]
  · have hn : ∀ j, k ≠ p j := fun j h => hk ⟨j, h.symm⟩
    simp [frame, OrClosure.frame, corePorts, hn,
      InputCellsCapacity.tapes_other p base remaining input output count k hn]

theorem capacityTrace (p : Ports K) (row : List Token) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (code : program again = statement p row again exit)
    (base : K → List Bool) (n : Nat) (input output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, register),
        InputCellsCapacity.tapes p base n input output count⟩) =
      some ⟨exit, (ambient, none), InputCellsCapacity.tapes p base 0 input
        ((tokenBits (repeatedRows row n)).reverse ++ output)
        (List.replicate (n * row.length) true ++ count)⟩ := by
  simpa only [List.append_nil, frame_eq_capacityTapes] using
    trace p row again exit program code (Function.update base (p 0) input)
      n [] output count ambient register

def inTime (p : Ports K) (row : List Token) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (code : program again = statement p row again exit)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, register), frame p base (encodeWord n ++ suffix) output count⟩
      (some ⟨exit, (ambient, none), frame p base (encodeWord 0 ++ suffix)
        ((tokenBits (repeatedRows row n)).reverse ++ output)
        (List.replicate (n * row.length) true ++ count)⟩) (n + 1) where
  steps := n + 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[n + 1] _ = _
    exact trace p row again exit program code base n suffix output count ambient register
  steps_le_m := Nat.le_refl _

section FixedVerifier

local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def blankRow (V : NPVerifier) : List Token :=
  (List.finRange (indexing V).symbolCount).map fun j =>
    let symbol := (indexing V).symbols.symm j
    .const (decide ((none : Option (V.computation.tm.Γ symbol.1)) = symbol.2))

@[simp] theorem blankRow_length (V : NPVerifier) :
    (blankRow V).length = (indexing V).symbolCount := by simp [blankRow]

theorem initialCellTokens_padding (V : NPVerifier) (input : List Bool) (S : Nat)
    (k : V.computation.tm.K) (i : Fin S) (a : Option (V.computation.tm.Γ k))
    (padding : (inputPrefix input).length + V.witnessBound.eval input.length ≤ i.val) :
    initialCellTokens V input S k i a = [.const (decide ((none : Option _) = a))] := by
  have hp : ¬ i.val < (inputPrefix input).length := by omega
  have hq : ¬ i.val - (inputPrefix input).length < V.witnessBound.eval input.length := by omega
  by_cases hk : k = V.computation.tm.k₀
  · subst k
    simp only [initialCellTokens, inputCellTokens, ite_eq_right hp, ite_eq_right hq, dite_eq_ite, ite_self]
  · simp [initialCellTokens, hk]

theorem cellRow_padding (V : NPVerifier) (input : List Bool) (S : Nat) (i : Fin S)
    (padding : (inputPrefix input).length + V.witnessBound.eval input.length ≤ i.val) :
    ((List.finRange (indexing V).symbolCount).flatMap fun j =>
      let symbol := (indexing V).symbols.symm j
      initialCellTokens V input S symbol.1 i symbol.2) = blankRow V := by
  simp only [initialCellTokens_padding V input S _ i _ padding]
  exact List.map_eq_flatMap.symm

def cellsInterval (V : NPVerifier) (input : List Bool) (S start n : Nat)
    (within : start + n ≤ S) : List Token :=
  (List.finRange n).flatMap fun i =>
    (List.finRange (indexing V).symbolCount).flatMap fun j =>
      let symbol := (indexing V).symbols.symm j
      initialCellTokens V input S symbol.1 ⟨start + i.val, by omega⟩ symbol.2

theorem cellsInterval_padding (V : NPVerifier) (input : List Bool) (S start n : Nat)
    (within : start + n ≤ S)
    (padding : (inputPrefix input).length + V.witnessBound.eval input.length ≤ start) :
    cellsInterval V input S start n within = repeatedRows (blankRow V) n := by
  unfold cellsInterval
  have hrow (i : Fin n) :
      ((List.finRange (indexing V).symbolCount).flatMap fun j =>
        let symbol := (indexing V).symbols.symm j
        initialCellTokens V input S symbol.1 ⟨start + i.val, by omega⟩ symbol.2) =
      blankRow V := cellRow_padding V input S _ (by
        change (inputPrefix input).length + V.witnessBound.eval input.length ≤ start + i.val
        omega)
  simp_rw [hrow]
  simp [List.flatMap_def, repeatedRows]

def verifierStatement (V : NPVerifier) (p : Ports K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  statement p (blankRow V) again exit

theorem verifierTrace (V : NPVerifier) (p : Ports K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (code : program again = verifierStatement V p again exit)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, register),
        frame p base (encodeWord n ++ suffix) output count⟩) =
      some ⟨exit, (ambient, none), frame p base (encodeWord 0 ++ suffix)
        ((tokenBits (repeatedRows (blankRow V) n)).reverse ++ output)
        (List.replicate (n * (indexing V).symbolCount) true ++ count)⟩ := by
  simpa only [blankRow_length] using
    trace p (blankRow V) again exit program code base n suffix output count ambient register

theorem paddingCellsTrace (V : NPVerifier) (input : List Bool) (S start n : Nat)
    (within : start + n ≤ S)
    (padding : (inputPrefix input).length + V.witnessBound.eval input.length ≤ start)
    (p : Ports K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (code : program again = verifierStatement V p again exit)
    (base : K → List Bool) (work output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, register),
        InputCellsCapacity.tapes p base n work output count⟩) =
      some ⟨exit, (ambient, none), InputCellsCapacity.tapes p base 0 work
        ((tokenBits (cellsInterval V input S start n within)).reverse ++ output)
        (List.replicate (n * (indexing V).symbolCount) true ++ count)⟩ := by
  rw [cellsInterval_padding V input S start n within padding]
  simpa only [blankRow_length] using
    capacityTrace p (blankRow V) again exit program code base n work output count ambient register

end FixedVerifier

variable [Fintype K] [Fintype σ]

def machine (p : Ports K) (row : List Token) (ambient : σ) : FinTM2 where
  K := K
  k₀ := p 3
  k₁ := p 1
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := σ × Option Bool
  initialState := (ambient, none)
  Γk₀Fin := inferInstance
  m _ := statement p row () none

theorem machineTrace (p : Ports K) (row : List Token) (base : K → List Bool)
    (n : Nat) (suffix output count : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (machine p row ambient).step)^[n + 1]
      (some ⟨some (), (ambient, register),
        frame p base (encodeWord n ++ suffix) output count⟩) =
      some ⟨none, (ambient, none), frame p base (encodeWord 0 ++ suffix)
        ((tokenBits (repeatedRows row n)).reverse ++ output)
        (List.replicate (n * row.length) true ++ count)⟩ :=
  trace p row () none (machine p row ambient).m rfl
    base n suffix output count ambient register

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PaddingCellsMachine

end

end OAI
