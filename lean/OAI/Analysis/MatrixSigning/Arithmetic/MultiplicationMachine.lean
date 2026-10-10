import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationLoop
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationNormalize
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationInitialize

namespace OAI

section

namespace KS.W03.MultiplicationMachine

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.MultiplicationBody KS.W03.BinaryAccumulator

def program : Program 7 :=
  compose (compose KS.W03.MultiplicationInitialize.program KS.W03.MultiplicationLoop.program)
    KS.W03.MultiplicationNormalize.program

def machine : Machine := program.toMachine

def exactBudget (xs ys : List Bool) : ℕ :=
  (KS.W03.MultiplicationInitialize.ticks xs ys + loopTicks xs ys []) +
    (2 * (loop xs ys []).length + 2)

theorem full_spec (xs ys : List Bool) :
    RunSpec program
      (registers (KS.W03.MultiplicationInitialize.inputBits xs ys) [] [] [] [] [] [])
      (registers [] [] (KS.W03.MultiplicationLoop.advance xs ys)
        (Computability.encodeNat (KS.W19.bitsValue xs * KS.W19.bitsValue ys)) [] [] [])
      (exactBudget xs ys) := by
  have hi := KS.W03.MultiplicationInitialize.initialize_spec xs ys
  have hl := KS.W03.MultiplicationLoop.loop_spec [] xs ys []
  have hn := KS.W03.MultiplicationNormalize.normalize_spec [] []
    (KS.W03.MultiplicationLoop.advance xs ys) (loop xs ys [])
  rw [loop_zero_correct] at hn
  exact (hi.compose hl).compose hn

@[simp] theorem stack_count : machine.stackCount = 7 := rfl
@[simp] theorem state_count : machine.states = 20 := rfl
@[simp] theorem input_port : machine.inputStack = (0 : Fin 7) := rfl
@[simp] theorem output_port : machine.outputStack = (3 : Fin 7) := rfl

theorem exactBudget_le (xs ys : List Bool) :
    exactBudget xs ys ≤ 16 * (xs.length + ys.length + 2) ^ 2 := by
  have ht := loop_zero_ticks_le xs ys
  have hl := loop_zero_length_le xs ys
  unfold exactBudget KS.W03.MultiplicationInitialize.ticks
  nlinarith [Nat.zero_le ((xs.length + ys.length) * (xs.length + ys.length))]

theorem exactBudget_le_input_polynomial (xs ys : List Bool) :
    exactBudget xs ys ≤ KS.W29.polynomialFuel 16 2
      (KS.W03.MultiplicationInitialize.inputBits xs ys).length := by
  have hl : xs.length + ys.length + 2 ≤
      (KS.W03.MultiplicationInitialize.inputBits xs ys).length + 1 := by
    rw [KS.W03.MultiplicationInitialize.inputBits_length]
    omega
  exact (exactBudget_le xs ys).trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hl 2))

theorem init_eq (xs ys : List Bool) :
    machine.init (KS.W03.MultiplicationInitialize.inputBits xs ys) =
      ⟨some program.initial,
        registers (KS.W03.MultiplicationInitialize.inputBits xs ys) [] [] [] [] [] []⟩ := by
  change Config.mk (some program.initial) _ = Config.mk (some program.initial) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_input (xs ys bits : List Bool) (hlen : exactBudget xs ys ≤ bits.length) :
    machine.run (machine.init (KS.W03.MultiplicationInitialize.inputBits xs ys)) bits =
      ⟨none, registers [] [] (KS.W03.MultiplicationLoop.advance xs ys)
        (Computability.encodeNat (KS.W19.bitsValue xs * KS.W19.bitsValue ys)) [] [] []⟩ := by
  rw [init_eq]
  exact (full_spec xs ys).run_of_le bits hlen

theorem output_correct (xs ys bits : List Bool)
    (hlen : exactBudget xs ys ≤ bits.length) :
    machine.output (KS.W03.MultiplicationInitialize.inputBits xs ys) bits =
      Computability.encodeNat (KS.W19.bitsValue xs * KS.W19.bitsValue ys) := by
  unfold Machine.output
  rw [run_input xs ys bits hlen]
  rfl

theorem halts_input_polynomial (xs ys : List Bool) :
    machine.HaltsWithin (KS.W03.MultiplicationInitialize.inputBits xs ys)
      (KS.W29.polynomialFuel 16 2 (KS.W03.MultiplicationInitialize.inputBits xs ys).length) := by
  intro seed
  change (machine.run (machine.init (KS.W03.MultiplicationInitialize.inputBits xs ys))
    (List.ofFn seed)).state = none
  rw [run_input xs ys (List.ofFn seed) (by
    simpa only [List.length_ofFn] using exactBudget_le_input_polynomial xs ys)]

theorem uniform_multiplication :
    ∃ M : Machine, M.stackCount = 7 ∧ M.states = 20 ∧
      ∀ xs ys : List Bool,
        M.HaltsWithin (KS.W03.MultiplicationInitialize.inputBits xs ys)
          (KS.W29.polynomialFuel 16 2 (KS.W03.MultiplicationInitialize.inputBits xs ys).length) ∧
        ∀ bits : List Bool,
          KS.W29.polynomialFuel 16 2 (KS.W03.MultiplicationInitialize.inputBits xs ys).length ≤ bits.length →
          M.output (KS.W03.MultiplicationInitialize.inputBits xs ys) bits =
            Computability.encodeNat (KS.W19.bitsValue xs * KS.W19.bitsValue ys) := by
  refine ⟨machine, rfl, rfl, ?_⟩
  intro xs ys
  refine ⟨halts_input_polynomial xs ys, ?_⟩
  intro bits hbits
  exact output_correct xs ys bits ((exactBudget_le_input_polynomial xs ys).trans hbits)

end KS.W03.MultiplicationMachine

end

end OAI
