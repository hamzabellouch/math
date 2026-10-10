import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryStackMoves
import OAI.Analysis.MatrixSigning.Arithmetic.RationalCompareCorrectness

namespace OAI

namespace KS.W04.CleanRationalCompare
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

variable {k : Nat}

def haltProgram (output : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) output output (fun _ _ _ => Instruction.halt k 1))

def clearState (port : Fin k) (before : Fin k → List Bool) : Fin k → List Bool :=
  fun j => if j = port then [] else before j

def clearListProgram (output : Fin k) : List (Fin k) → Program k
  | [] => haltProgram output
  | port :: ports => compose (BinaryStackMoves.clearProgram port) (clearListProgram output ports)

def clearListState : List (Fin k) → (Fin k → List Bool) → (Fin k → List Bool)
  | [], before => before
  | port :: ports, before => clearListState ports (clearState port before)

def clearListTicks : List (Fin k) → (Fin k → List Bool) → Nat
  | [], _ => 1
  | port :: ports, before => (before port).length + 1 + clearListTicks ports (clearState port before)

theorem halt_spec (output : Fin k) (before : Fin k → List Bool) :
    RunSpec (haltProgram output) before before 1 := by
  intro bits hlen
  obtain ⟨coin, rfl⟩ := List.length_eq_one_iff.mp hlen
  change (compile (0 : Fin 1) output output (fun _ _ _ => Instruction.halt k 1)).step
    ⟨some (0 : Fin 1), before⟩ coin = ⟨none, before⟩
  erw [step_compile]
  apply congrArg (Config.mk none)
  funext j
  simp [Instruction.halt, Instruction.action, KS.W29.StackAction.apply]

theorem clear_spec (port : Fin k) (before : Fin k → List Bool) :
    RunSpec (BinaryStackMoves.clearProgram port) before (clearState port before)
      ((before port).length + 1) := by
  intro bits hlen
  exact BinaryStackMoves.run_clear_stacks port before bits hlen

theorem clearList_spec (output : Fin k) (ports : List (Fin k)) (before : Fin k → List Bool) :
    RunSpec (clearListProgram output ports) before (clearListState ports before)
      (clearListTicks ports before) := by
  induction ports generalizing before with
  | nil => exact halt_spec output before
  | cons p ps ih => exact (clear_spec p before).compose (ih (clearState p before))

theorem clearListState_apply (ports : List (Fin k)) (before : Fin k → List Bool) (j : Fin k) :
    clearListState ports before j = if j ∈ ports then [] else before j := by
  induction ports generalizing before with
  | nil => simp [clearListState]
  | cons p ps ih =>
      simp only [clearListState, ih, List.mem_cons]
      by_cases hj : j ∈ ps <;> by_cases hp : j = p <;> simp [clearState, hj, hp]

theorem clearListTicks_le (ports : List (Fin k)) (before : Fin k → List Bool)
    (bound : Nat) (hbound : ∀ j, (before j).length ≤ bound) :
    clearListTicks ports before ≤ ports.length * (bound + 1) + 1 := by
  induction ports generalizing before with
  | nil => simp [clearListTicks]
  | cons p ps ih =>
      have hm : ∀ j, (clearState p before j).length ≤ bound := by
        intro j
        by_cases hj : j = p <;> simp [clearState, hj, hbound j]
      have h := ih (clearState p before) hm
      have hp := hbound p
      simp only [clearListTicks, List.length_cons]
      nlinarith

def scratchPorts : List (Fin 13) := [0,1,2,3,4,5,6,7,8,10,11,12]
def cleanupProgram : Program 13 := clearListProgram 9 scratchPorts

def flagState (flag : Bool) : Fin 13 → List Bool := fun j => if j = 9 then [flag] else []

def canonicalFinal (q r : ℚ) : Fin 13 → List Bool :=
  KS.W06.RationalCompare.finalStacks
    (KS.W06.RationalCompare.negativeBit q.num) (KS.W06.RationalCompare.constructorBits q.num)
    (Computability.encodeNat q.den) (KS.W06.RationalCompare.negativeBit r.num)
    (KS.W06.RationalCompare.constructorBits r.num) (Computability.encodeNat r.den)

def inputState (q r : ℚ) : Fin 13 → List Bool :=
  KS.W06.RationalCompare.fields (KS.W01.encodeRat q ++ KS.W01.encodeRat r) [] [] [] [] [] []

def comparisonTicks (q r : ℚ) : Nat :=
  KS.W29.polynomialFuel 128 2 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length

theorem canonical_spec (q r : ℚ) :
    RunSpec KS.W06.RationalCompare.program (inputState q r) (canonicalFinal q r)
      (comparisonTicks q r) := by
  have h := KS.W06.RationalCompare.full_spec
    (KS.W06.RationalCompare.negativeBit q.num) (KS.W06.RationalCompare.constructorBits q.num)
    (Computability.encodeNat q.den) (KS.W06.RationalCompare.negativeBit r.num)
    (KS.W06.RationalCompare.constructorBits r.num) (Computability.encodeNat r.den)
  rw [KS.W06.RationalCompare.pairBits_encodeRat] at h
  apply h.mono
  have ht := KS.W06.RationalCompare.totalTicks_le_polynomial
    (KS.W06.RationalCompare.negativeBit q.num) (KS.W06.RationalCompare.constructorBits q.num)
    (Computability.encodeNat q.den) (KS.W06.RationalCompare.negativeBit r.num)
    (KS.W06.RationalCompare.constructorBits r.num) (Computability.encodeNat r.den)
  simp only [KS.W06.RationalCompare.pairBits_encodeRat] at ht
  exact ht

theorem canonicalFinal_length (q r : ℚ) (j : Fin 13) :
    (canonicalFinal q r j).length ≤
      (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + comparisonTicks q r := by
  let bits := List.replicate (comparisonTicks q r) false
  have hr := canonical_spec q r bits (by simp [bits])
  have hg := KS.W06.RationalCompare.program.toMachine.run_stack_length_le
    ⟨some KS.W06.RationalCompare.program.initial, inputState q r⟩ bits j
  rw [hr] at hg
  have hi : (inputState q r j).length ≤ (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
    fin_cases j <;> simp [inputState, KS.W06.RationalCompare.fields]
  simpa only [bits, List.length_replicate] using hg.trans (Nat.add_le_add_right hi _)

theorem clear_canonicalFinal (q r : ℚ) :
    clearListState scratchPorts (canonicalFinal q r) = flagState (decide (q ≤ r)) := by
  funext j
  rw [clearListState_apply]
  fin_cases j <;> simp [scratchPorts, flagState]
  exact KS.W06.RationalCompare.canonical_final_output q r

def cleanedComparator : Program 13 := compose KS.W06.RationalCompare.program cleanupProgram

def totalTicks (q r : ℚ) : Nat :=
  comparisonTicks q r + clearListTicks scratchPorts (canonicalFinal q r)

theorem cleaned_spec (q r : ℚ) :
    RunSpec cleanedComparator (inputState q r) (flagState (decide (q ≤ r))) (totalTicks q r) := by
  have h := (canonical_spec q r).compose (clearList_spec 9 scratchPorts (canonicalFinal q r))
  rw [clear_canonicalFinal] at h
  exact h

theorem totalTicks_le_polynomial (q r : ℚ) :
    totalTicks q r ≤ KS.W29.polynomialFuel 2048 2
      (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
  have h := clearListTicks_le scratchPorts (canonicalFinal q r)
    ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + comparisonTicks q r)
    (canonicalFinal_length q r)
  change clearListTicks scratchPorts (canonicalFinal q r) ≤
    12 * ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + comparisonTicks q r + 1) + 1 at h
  dsimp only [totalTicks, comparisonTicks, KS.W29.polynomialFuel] at h ⊢
  nlinarith [Nat.zero_le ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length ^ 2)]

theorem cleaned_polynomial_spec (q r : ℚ) :
    RunSpec cleanedComparator (inputState q r) (flagState (decide (q ≤ r)))
      (KS.W29.polynomialFuel 2048 2 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) :=
  (cleaned_spec q r).mono (totalTicks_le_polynomial q r)

@[simp] theorem cleaned_output : cleanedComparator.output = 9 := rfl

end KS.W04.CleanRationalCompare

end OAI
