import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticEncodingSize
import OAI.Analysis.MatrixSigning.Arithmetic.SignedRationalSerializer
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMultiplyNormalize

namespace OAI

section

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program : Program 13 :=
  compose normalizeProgram KS.W01.SignedRationalSerializer.program

def machine : Machine := program.toMachine

def inputBits (q r : ℚ) : List Bool := KS.W01.encodeRat q ++ KS.W01.encodeRat r

def totalTicks (q r : ℚ) : Nat :=
  canonicalNormalizeTicks q r + 16 *
    ((Computability.encodeNat (q * r).num.natAbs).length +
      (Computability.encodeNat (q * r).den).length + 1)

theorem full_spec (q r : ℚ) :
    RunSpec program (KS.W06.RationalCompare.fields (inputBits q r) [] [] [] [] [] [])
      (KS.W01.SignedRationalSerializer.outputState (KS.W01.encodeRat (q * r)))
      (totalTicks q r) :=
  (canonical_normalized_spec q r).compose (KS.W01.SignedRationalSerializer.serializes_rational (q * r))

@[simp] theorem machine_stackCount : machine.stackCount = 13 := rfl
@[simp] theorem machine_inputStack : machine.inputStack = (0 : Fin 13) := rfl
@[simp] theorem machine_outputStack : machine.outputStack = (10 : Fin 13) := rfl

theorem compose_table_length {k : Nat} (P Q : Program k) :
    (compose P Q).table.length = (compose P Q).states * (3 ^ k * 2) := by
  change (KS.W01.FixedStack.compile (leftState P Q P.initial) P.input Q.output
    (KS.W29.FixedSequential.dispatch P Q)).table.length = _
  exact KS.W01.FixedStack.compile_table_length _ _ _ _

theorem program_table_length : program.table.length = program.states * (3 ^ 13 * 2) :=
  compose_table_length normalizeProgram KS.W01.SignedRationalSerializer.program

theorem init_eq (bits : List Bool) :
    machine.init bits =
      ⟨some program.initial, KS.W06.RationalCompare.fields bits [] [] [] [] [] []⟩ := by
  apply congrArg (Config.mk (some program.initial))
  funext j
  fin_cases j <;> rfl

theorem run_input (q r : ℚ) (bits : List Bool) (hlen : totalTicks q r ≤ bits.length) :
    machine.run (machine.init (inputBits q r)) bits =
      ⟨none, KS.W01.SignedRationalSerializer.outputState (KS.W01.encodeRat (q * r))⟩ := by
  rw [init_eq]
  exact (full_spec q r).run_of_le bits hlen

theorem output_correct (q r : ℚ) (bits : List Bool) (hlen : totalTicks q r ≤ bits.length) :
    machine.output (inputBits q r) bits = KS.W01.encodeRat (q * r) := by
  unfold Machine.output
  rw [run_input q r bits hlen]
  rfl

theorem lifted_full_spec {k : Nat} (ports : Fin 13 ↪ Fin k)
    (before : Fin k → List Bool) (q r : ℚ)
    (hin : before (ports 0) = inputBits q r)
    (hwork : ∀ i : Fin 13, i ≠ 0 → before (ports i) = []) :
    RunSpec (KS.W29.FixedSequential.liftPorts program ports) before
      (KS.W06.RationalCompare.replacePorts ports before
        (KS.W01.SignedRationalSerializer.outputState (KS.W01.encodeRat (q * r))))
      (totalTicks q r) := by
  have heq : (fun i => before (ports i)) =
      KS.W06.RationalCompare.fields (inputBits q r) [] [] [] [] [] [] := by
    funext i
    fin_cases i
    · exact hin
    all_goals exact hwork _ (by decide)
  apply KS.W06.RationalCompare.runSpec_liftPorts
  rw [heq]
  exact full_spec q r

theorem totalTicks_le_polynomial (q r : ℚ) :
    totalTicks q r ≤ KS.W29.polynomialFuel 2048 3 (inputBits q r).length := by
  have hn := canonicalNormalizeTicks_le q r
  obtain ⟨hp, hd⟩ := KS.W01.mul_parts_size_le q r
  have hl : KS.W01.ratLength q + KS.W01.ratLength r = (inputBits q r).length := by
    simp [inputBits, KS.W01.ratLength]
  rw [hl] at hp hd
  let N := (inputBits q r).length + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hpow : N ≤ N ^ 3 := by
    calc
      N = N ^ 1 := by simp
      _ ≤ N ^ 3 := Nat.pow_le_pow_right hN (by decide)
  change canonicalNormalizeTicks q r +
      16 * ((Computability.encodeNat (q * r).num.natAbs).length +
        (Computability.encodeNat (q * r).den).length + 1) ≤ 2048 * N ^ 3
  simp only [KS.W19.encodeNat_length_eq_size]
  change canonicalNormalizeTicks q r ≤ 1024 * N ^ 3 at hn
  change Nat.size (q * r).num.natAbs ≤ N at hp
  change Nat.size (q * r).den ≤ N at hd
  omega

theorem halts_input_polynomial (q r : ℚ) :
    machine.HaltsWithin (inputBits q r)
      (KS.W29.polynomialFuel 2048 3 (inputBits q r).length) := by
  intro seed
  change (machine.run (machine.init (inputBits q r)) (List.ofFn seed)).state = none
  rw [run_input q r (List.ofFn seed) (by
    simpa only [List.length_ofFn] using totalTicks_le_polynomial q r)]

theorem uniform_rational_multiplication :
    ∃ M : Machine, M.stackCount = 13 ∧ M.inputStack.val = 0 ∧ M.outputStack.val = 10 ∧
      ∀ q r : ℚ,
        M.HaltsWithin (KS.W01.encodeRat q ++ KS.W01.encodeRat r)
          (KS.W29.polynomialFuel 2048 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) ∧
        ∀ bits : List Bool,
          KS.W29.polynomialFuel 2048 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length ≤
            bits.length →
          M.output (KS.W01.encodeRat q ++ KS.W01.encodeRat r) bits = KS.W01.encodeRat (q * r) := by
  refine ⟨machine, rfl, rfl, rfl, ?_⟩
  intro q r
  refine ⟨halts_input_polynomial q r, ?_⟩
  intro bits hbits
  exact output_correct q r bits ((totalTicks_le_polynomial q r).trans hbits)

end KS.W15.RationalMultiply

end

end OAI
