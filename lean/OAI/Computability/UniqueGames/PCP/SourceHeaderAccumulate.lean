import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

structure Layout (K : Type) where
  bits : K
  count : K
  accumulator : K
  bits_count : bits ≠ count
  bits_accumulator : bits ≠ accumulator
  count_accumulator : count ≠ accumulator

variable {K Λ σ : Type} [DecidableEq K]

def statement (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ) :
    Bool → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | false => loopAt layout.bits layout.accumulator id false (labels false) (some (labels true))
  | true => loopAt layout.count layout.accumulator id false (labels true) exit

def resultTapes (layout : Layout K) (base : K → List Bool) (nBits count : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base layout.bits []) layout.count [])
    layout.accumulator ((encodeWords [nBits, count]).reverse ++ base layout.accumulator)

@[simp] theorem result_bits (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.bits = [] := by
  simp [resultTapes, layout.bits_count, layout.bits_accumulator]

@[simp] theorem result_count (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.count = [] := by
  simp [resultTapes, layout.count_accumulator]

@[simp] theorem result_accumulator (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.accumulator =
      (encodeWords [nBits, count]).reverse ++ base layout.accumulator := by
  simp [resultTapes]

theorem result_frame (layout : Layout K) (base : K → List Bool) (nBits count : Nat)
    (k : K) (hb : k ≠ layout.bits) (hc : k ≠ layout.count) (ha : k ≠ layout.accumulator) :
    resultTapes layout base nBits count k = base k := by
  simp [resultTapes, hb, hc, ha]

theorem trace (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[nBits + count + 4]
      (some ⟨some (labels false), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), resultTapes layout base nBits count⟩ := by
  let middle := tapesAt layout.bits layout.accumulator base []
    ((encodeWord nBits).reverse ++ base layout.accumulator)
  have firstRun := transferAt_fromTapes layout.bits layout.accumulator layout.bits_accumulator
    id false (labels false) (some (labels true)) program (by simpa only [statement] using atLabels false) base ambient register
  change (advance (TM2.step program))^[(base layout.bits).length + 1]
    (some ⟨some (labels false), (ambient, register), base⟩) = _ at firstRun
  simp only [hbits, List.map_id, encodeWord_length] at firstRun
  have hc : middle layout.count = encodeWord count := by
    dsimp only [middle]
    rw [tapesAt_other _ _ _ layout.bits_count.symm layout.count_accumulator]
    exact hcount
  have ha : middle layout.accumulator =
      (encodeWord nBits).reverse ++ base layout.accumulator := by
    exact tapesAt_dst _ _ _ _ _
  have secondRun := transferAt_fromTapes layout.count layout.accumulator layout.count_accumulator
    id false (labels true) exit program (by simpa only [statement] using atLabels true) middle ambient none
  change (advance (TM2.step program))^[(middle layout.count).length + 1]
    (some ⟨some (labels true), (ambient, none), middle⟩) = _ at secondRun
  simp only [hc, ha, List.map_id, encodeWord_length] at secondRun
  have he : tapesAt layout.count layout.accumulator middle []
      ((encodeWord count).reverse ++ ((encodeWord nBits).reverse ++ base layout.accumulator)) =
      resultTapes layout base nBits count := by
    funext k
    by_cases hk : k = layout.accumulator
    · subst k
      simp [resultTapes, tapesAt, encodeWords, List.reverse_append, List.append_assoc]
    · by_cases hc : k = layout.count
      · subst k; simp [tapesAt, resultTapes, layout.count_accumulator]
      · by_cases hb : k = layout.bits
        · subst k
          simp [middle, tapesAt, resultTapes, layout.bits_count, layout.bits_accumulator]
        · simp [middle, tapesAt, resultTapes, hk, hc, hb]
  rw [he] at secondRun
  rw [show nBits + count + 4 = (count + 1 + 1) + (nBits + 1 + 1) by omega,
    Function.iterate_add_apply, firstRun]
  exact secondRun

def inTime (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels false), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), resultTapes layout base nBits count⟩)
      (nBits + count + 4) where
  steps := nBits + count + 4
  evals_in_steps := trace layout labels exit program atLabels base nBits count hbits hcount ambient register
  steps_le_m := Nat.le_refl _

@[simp] theorem inTime_steps (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    (inTime layout labels exit program atLabels base nBits count hbits hcount ambient register).steps =
      nBits + count + 4 := rfl

def machine [Fintype K] [Fintype σ] (layout : Layout K) (ambient : σ) : FinTM2 where
  K := K
  k₀ := layout.bits
  k₁ := layout.accumulator
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := σ × Option Bool
  initialState := (ambient, none)
  m := statement layout id none

theorem source_inputBits_header (input : UniqueGamesTheorem.Reduction.SourceEncoding.Input) :
    UniqueGamesTheorem.Reduction.SourceEncoding.inputBits input =
      encodeWords [input.variables, input.equations.length] ++
        encodeWords (input.equations.flatMap UniqueGamesTheorem.Reduction.SourceEncoding.equationWords) := by
  simp only [UniqueGamesTheorem.Reduction.SourceEncoding.inputBits,
    UniqueGamesTheorem.Reduction.SourceEncoding.inputWords, encodeWords_append]

end UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate

end

end OAI
