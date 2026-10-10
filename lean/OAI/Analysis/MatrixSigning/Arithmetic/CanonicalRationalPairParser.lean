import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.SingleRationalParser

namespace OAI

section

namespace KS.W06.CanonicalRationalPairParser
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare

def program : Program 13 := prepareProgram
def machine : Machine := program.toMachine
def inputState (input : List Bool) : Fin 13 → List Bool := fields input [] [] [] [] [] []
def state (q r : ℚ) : Fin 13 → List Bool :=
  workFields [decide (q.num < 0)] (Computability.encodeNat q.num.natAbs)
    (Computability.encodeNat q.den) [decide (r.num < 0)]
    (Computability.encodeNat r.num.natAbs) (Computability.encodeNat r.den) [] []

theorem canonical_pair_spec (q r : ℚ) :
    RunSpec program (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r)) (state q r)
      (8 * (KS.W01.ratLength q + KS.W01.ratLength r + 1)) := by
  have h := prepare_spec (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
    (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den)
  rw [pairBits_encodeRat] at h
  simp only [magnitude, SingleRationalParser.magnitude_constructor_eq] at h
  apply h.mono
  have hlen := congrArg List.length (pairBits_encodeRat q r)
  rw [pairBits_length, List.length_append] at hlen
  unfold parseTicks KS.W01.ratLength
  omega

theorem onPorts_spec {k : ℕ} (ports : Fin 13 ↪ Fin k) (before : Fin k → List Bool)
    (q r : ℚ)
    (hbefore : (fun i => before (ports i)) = inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r)) :
    RunSpec (KS.W29.FixedSequential.liftPorts program ports) before
      (replacePorts ports before (state q r))
      (8 * (KS.W01.ratLength q + KS.W01.ratLength r + 1)) := by
  apply runSpec_liftPorts
  rw [hbefore]
  exact canonical_pair_spec q r

theorem init_eq (input : List Bool) : machine.init input = ⟨some program.initial, inputState input⟩ := by
  apply congrArg (Config.mk (some program.initial))
  funext i
  fin_cases i <;> rfl

theorem run_input (q r : ℚ) (bits : List Bool)
    (hlen : 8 * (KS.W01.ratLength q + KS.W01.ratLength r + 1) ≤ bits.length) :
    machine.run (machine.init (KS.W01.encodeRat q ++ KS.W01.encodeRat r)) bits = ⟨none, state q r⟩ := by
  rw [init_eq]
  exact (canonical_pair_spec q r).run_of_le bits hlen

end KS.W06.CanonicalRationalPairParser

end

end OAI
