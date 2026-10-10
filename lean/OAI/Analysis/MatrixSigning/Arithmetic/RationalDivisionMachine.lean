import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalDivisionStages

namespace OAI

section

namespace KS.W30.RationalDivision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program : Program 15 := compose parseNumerator (compose storeDenominator
  (compose serializeNumerator (compose storeNumerator (compose restoreDenominator
    (compose reciprocal (compose prepareInverse (compose prependNumerator multiply)))))))
def machine : Machine := program.toMachine

def totalTicks (q r : ℚ) : ℕ :=
  8 * (KS.W01.ratLength q + 1) + ((2 * KS.W01.ratLength r + 2) +
    (serializerTicks q + ((2 * KS.W01.ratLength q + 2) + ((2 * KS.W01.ratLength r + 2) +
      (1000 * (KS.W01.ratLength r + 1) ^ 3 + ((2 * KS.W01.ratLength r⁻¹ + 2) +
        ((2 * KS.W01.ratLength q + 2) + KS.W15.RationalMultiply.totalTicks q r⁻¹)))))))

theorem full_spec (q r : ℚ) :
    RunSpec program (inputState (inputBits q r))
      (outputState (KS.W01.encodeRat (q / r))) (totalTicks q r) :=
  (parseNumerator_spec q r).compose ((storeDenominator_spec q r).compose
    ((serializeNumerator_spec q r).compose ((storeNumerator_spec q r).compose
      ((restoreDenominator_spec q r).compose ((reciprocal_spec q r).compose
        ((prepareInverse_spec q r).compose ((prependNumerator_spec q r).compose (multiply_spec q r))))))))

theorem totalTicks_le_polynomial (q r : ℚ) :
    totalTicks q r ≤ KS.W29.polynomialFuel 1100000 3 (inputBits q r).length := by
  let N := KS.W01.ratLength q + KS.W01.ratLength r + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) N
  have hinv := KS.W01.ratLength_inv_le r
  have hparts := KS.W01.rational_parts_size_le_length q
  have hserial : serializerTicks q ≤ 48 * (KS.W01.ratLength q + 1) := by
    simp only [serializerTicks, KS.W19.encodeNat_length_eq_size]
    omega
  have hsmall : KS.W01.ratLength r + 1 ≤ N := by dsimp [N]; omega
  have hrecip : 1000 * (KS.W01.ratLength r + 1) ^ 3 ≤ 1000 * N ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsmall _)
  have hpair : (KS.W15.RationalMultiply.inputBits q r⁻¹).length + 1 ≤ 8 * N := by
    simp only [KS.W15.RationalMultiply.inputBits, List.length_append]
    change KS.W01.ratLength q + KS.W01.ratLength r⁻¹ + 1 ≤ 8 * N
    dsimp [N]
    omega
  have hmul : KS.W15.RationalMultiply.totalTicks q r⁻¹ ≤ 1048576 * N ^ 3 := by
    calc
      _ ≤ 2048 * ((KS.W15.RationalMultiply.inputBits q r⁻¹).length + 1) ^ 3 :=
        KS.W15.RationalMultiply.totalTicks_le_polynomial q r⁻¹
      _ ≤ 2048 * (8 * N) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpair _)
      _ = 1048576 * N ^ 3 := by ring
  have hother : 8 * (KS.W01.ratLength q + 1) + (2 * KS.W01.ratLength r + 2) +
      serializerTicks q + (2 * KS.W01.ratLength q + 2) + (2 * KS.W01.ratLength r + 2) +
      (2 * KS.W01.ratLength r⁻¹ + 2) + (2 * KS.W01.ratLength q + 2) ≤ 100 * N := by
    dsimp [N]
    omega
  change totalTicks q r ≤ 1100000 * ((inputBits q r).length + 1) ^ 3
  have hlen : (inputBits q r).length + 1 = N := by
    simp only [inputBits, List.length_append, N, KS.W01.ratLength]
  rw [hlen]
  unfold totalTicks
  omega

theorem program_spec (q r : ℚ) :
    RunSpec program (inputState (inputBits q r))
      (outputState (KS.W01.encodeRat (q / r)))
      (KS.W29.polynomialFuel 1100000 3 (inputBits q r).length) :=
  (full_spec q r).mono (totalTicks_le_polynomial q r)

theorem init_eq (wire : List Bool) :
    machine.init wire = ⟨some program.initial, inputState wire⟩ := by
  apply KS.W19.FixedRun.config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem run_input (q r : ℚ) (bits : List Bool)
    (hlen : KS.W29.polynomialFuel 1100000 3 (inputBits q r).length ≤ bits.length) :
    machine.run (machine.init (inputBits q r)) bits =
      ⟨none, outputState (KS.W01.encodeRat (q / r))⟩ := by
  rw [init_eq]
  exact (program_spec q r).run_of_le bits hlen

theorem output_correct (q r : ℚ) (bits : List Bool)
    (hlen : KS.W29.polynomialFuel 1100000 3 (inputBits q r).length ≤ bits.length) :
    machine.output (inputBits q r) bits = KS.W01.encodeRat (q / r) := by
  unfold Machine.output
  rw [run_input q r bits hlen]
  rfl

theorem halts_input_polynomial (q r : ℚ) :
    machine.HaltsWithin (inputBits q r)
      (KS.W29.polynomialFuel 1100000 3 (inputBits q r).length) := by
  intro seed
  unfold Machine.runSeed
  exact congrArg Config.state (run_input q r (List.ofFn seed) (by simp))

theorem uniform_rational_division :
    ∃ M : Machine, M.stackCount = 15 ∧ M.inputStack.val = 0 ∧ M.outputStack.val = 10 ∧
      ∀ q r : ℚ,
        M.HaltsWithin (KS.W01.encodeRat q ++ KS.W01.encodeRat r)
          (KS.W29.polynomialFuel 1100000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) ∧
        ∀ bits : List Bool,
          KS.W29.polynomialFuel 1100000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length ≤
            bits.length →
          M.output (KS.W01.encodeRat q ++ KS.W01.encodeRat r) bits = KS.W01.encodeRat (q / r) := by
  refine ⟨machine, rfl, rfl, rfl, ?_⟩
  intro q r
  exact ⟨halts_input_polynomial q r, fun bits hbits => output_correct q r bits hbits⟩

def onPorts {k : ℕ} (ports : Fin 15 ↪ Fin k) : Program k :=
  KS.W29.FixedSequential.liftPorts program ports

theorem onPorts_spec {k : ℕ} (ports : Fin 15 ↪ Fin k)
    (before : Fin k → List Bool) (q r : ℚ)
    (hbefore : (fun i => before (ports i)) = inputState (inputBits q r)) :
    RunSpec (onPorts ports) before
      (KS.W06.RationalCompare.replacePorts ports before (outputState (KS.W01.encodeRat (q / r))))
      (KS.W29.polynomialFuel 1100000 3 (inputBits q r).length) := by
  apply KS.W06.RationalCompare.runSpec_liftPorts program ports before _ _
  rw [hbefore]
  exact program_spec q r

end KS.W30.RationalDivision

end

end OAI
