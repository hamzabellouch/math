import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.SingleRationalParser
import OAI.Analysis.MatrixSigning.Arithmetic.RationalReciprocalSerialize

namespace OAI

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program : Program 13 := compose KS.W06.SingleRationalParser.program serializeCore
def machine : Machine := program.toMachine

def inputState (wire : List Bool) : Fin 13 → List Bool :=
  KS.W06.SingleRationalParser.inputState wire

def outputState (wire : List Bool) : Fin 13 → List Bool :=
  KS.W01.SignedRationalSerializer.outputState wire

theorem program_spec (q : ℚ) :
    RunSpec program (inputState (KS.W01.encodeRat q))
      (outputState (KS.W01.encodeRat q⁻¹))
      (1000 * (KS.W01.ratLength q + 1) ^ 3) := by
  have hp : RunSpec KS.W06.SingleRationalParser.program
      (inputState (KS.W01.encodeRat q)) (canonicalState q)
      (8 * (KS.W01.ratLength q + 1)) := by
    have h := KS.W06.SingleRationalParser.canonical_spec q []
    simp only [List.append_nil] at h
    exact h
  have h := hp.compose (serializeCore_spec q)
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (KS.W01.ratLength q + 1)
  exact h.mono (by omega)

theorem init_eq (wire : List Bool) :
    machine.init wire = ⟨some program.initial, inputState wire⟩ := by
  apply KS.W19.FixedRun.config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem run_polynomial (q : ℚ) (bits : List Bool)
    (hlen : bits.length = KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q).length) :
    machine.run (machine.init (KS.W01.encodeRat q)) bits =
      ⟨none, outputState (KS.W01.encodeRat q⁻¹)⟩ := by
  rw [init_eq]
  apply (program_spec q).run_of_le bits
  exact le_of_eq (by simpa only [KS.W29.polynomialFuel, KS.W01.ratLength] using hlen.symm)

theorem haltsWithin_polynomial (q : ℚ) :
    machine.HaltsWithin (KS.W01.encodeRat q)
      (KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q).length) := by
  intro seed
  unfold Machine.runSeed
  have h := run_polynomial q (List.ofFn seed) (by simp only [List.length_ofFn])
  exact congrArg Config.state h

theorem output_polynomial (q : ℚ) (bits : List Bool)
    (hlen : bits.length = KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q).length) :
    machine.output (KS.W01.encodeRat q) bits = KS.W01.encodeRat q⁻¹ := by
  unfold Machine.output
  rw [run_polynomial q bits hlen]
  rfl

theorem output_of_sufficient_length (q : ℚ) (bits : List Bool)
    (hlen : KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q).length ≤ bits.length) :
    machine.output (KS.W01.encodeRat q) bits = KS.W01.encodeRat q⁻¹ := by
  unfold Machine.output
  rw [init_eq]
  erw [(program_spec q).run_of_le bits hlen]
  rfl

theorem uniform_rational_reciprocal :
    ∃ M : Machine, M.stackCount = 13 ∧ M.inputStack.val = 0 ∧ M.outputStack.val = 10 ∧
      ∀ q : ℚ,
        M.HaltsWithin (KS.W01.encodeRat q)
          (KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q).length) ∧
        ∀ bits : List Bool,
          KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q).length ≤ bits.length →
          M.output (KS.W01.encodeRat q) bits = KS.W01.encodeRat q⁻¹ := by
  refine ⟨machine, rfl, rfl, rfl, ?_⟩
  intro q
  exact ⟨haltsWithin_polynomial q, fun bits hbits => output_of_sufficient_length q bits hbits⟩

def onPorts {k : ℕ} (ports : Fin 13 ↪ Fin k) : Program k :=
  KS.W29.FixedSequential.liftPorts program ports

theorem onPorts_spec {k : ℕ} (ports : Fin 13 ↪ Fin k)
    (before : Fin k → List Bool) (q : ℚ)
    (hbefore : (fun i => before (ports i)) = inputState (KS.W01.encodeRat q)) :
    RunSpec (onPorts ports) before
      (KS.W06.RationalCompare.replacePorts ports before
        (outputState (KS.W01.encodeRat q⁻¹)))
      (1000 * (KS.W01.ratLength q + 1) ^ 3) := by
  apply KS.W06.RationalCompare.runSpec_liftPorts program ports before _ _
  rw [hbefore]
  exact program_spec q

end KS.W30.RationalReciprocal

end OAI
