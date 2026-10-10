import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRecorderGates
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingAddressGrowth

namespace OAI

/-! The complete instruction array has at most one gate per source address.
This exponential bound will pay for summing all gate derivatives. -/

namespace ForcedComputation.ExpandingDetector
open Recorder

theorem stageWire_card_le (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ) :
    Fintype.card (StageWire M hM blank d) ≤
      (allControls M).length * (alphabetBase M blank ^ d) ^ 2 := by
  let f : StageWire M hM blank d →
      Fin ((allControls M).length * (alphabetBase M blank ^ d) ^ 2) :=
    fun w => w.val.1.toAddress.finIndex
  have hf : Function.Injective f := by
    intro w z hwz
    apply StageWire.source_injective M hM blank d
    apply RecorderAddress.number_injective M blank d
    exact congrArg Address.index (Address.finIndex_injective _ _ hwz)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem stageWire_card_growth (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m n : ℕ) :
    Fintype.card (StageWire M hM blank (m + n)) ≤
      addressFactor M blank m * addressGrowth M blank ^ n := by
  apply (stageWire_card_le M hM blank (m + n)).trans_eq
  unfold addressFactor addressGrowth
  rw [pow_add, mul_pow]
  simp only [← pow_mul]
  rw [Nat.mul_comm m 2, Nat.mul_comm n 2]
  ring

theorem stageWire_card_growth_real (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m n : ℕ) :
    (Fintype.card (StageWire M hM blank (m + n)) : ℝ) ≤
      (addressFactor M blank m : ℝ) * (addressGrowth M blank : ℝ) ^ n := by
  exact_mod_cast stageWire_card_growth M hM blank m n

end ForcedComputation.ExpandingDetector

end OAI
