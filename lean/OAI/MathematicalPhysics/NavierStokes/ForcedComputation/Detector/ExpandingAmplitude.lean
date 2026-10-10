import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingWorkBudget

namespace OAI

/-! One amplitude budget controls each gate and the sum of all gates in a
stage. The latter decays geometrically despite the growing address set. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open Recorder

def stageAmplitude (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m n : ℕ) : ℝ :=
  ((addressFactor M blank m : ℝ) * (addressGrowth M blank : ℝ)^(n+1) + 2) /
    (workFactor M blank m * workGrowth M blank ^ (n+1) + 2)

theorem workGrowth_ge_addressGrowth (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) :
    (addressGrowth M blank : ℝ) ≤ workGrowth M blank := by
  have hA : (1 : ℝ) ≤ addressGrowth M blank := by exact_mod_cast addressGrowth_ge_one M blank
  unfold workGrowth
  nlinarith

theorem workFactor_ge_addressFactor (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ) :
    (addressFactor M blank m : ℝ) ≤ workFactor M blank m := by
  have hF : (0 : ℝ) ≤ addressFactor M blank m := Nat.cast_nonneg _
  unfold workFactor
  nlinarith [sq_nonneg (addressFactor M blank m : ℝ)]

theorem stageAmplitude_nonneg (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m n : ℕ) :
    0 ≤ stageAmplitude M blank m n := by
  unfold stageAmplitude
  apply div_nonneg
  · positivity
  · have hK := workFactor_nonneg M blank m
    have hD := workGrowth_ge_one M blank
    positivity

theorem stageAmplitude_le_one (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m n : ℕ) :
    stageAmplitude M blank m n ≤ 1 := by
  have hK := workFactor_nonneg M blank m
  have hD := workGrowth_ge_one M blank
  have hF : (0 : ℝ) ≤ addressFactor M blank m := Nat.cast_nonneg _
  have hA : (0 : ℝ) ≤ addressGrowth M blank := Nat.cast_nonneg _
  have hp := pow_le_pow_left₀ hA (workGrowth_ge_addressGrowth M blank) (n+1)
  unfold stageAmplitude
  apply (div_le_one (by positivity)).mpr
  linarith [mul_le_mul (workFactor_ge_addressFactor M blank m) hp (pow_nonneg hA _) hK]

theorem stageAmplitude_total_bound (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m n : ℕ) :
    (Fintype.card (StageWire M hM blank (m+n)) : ℝ) * stageAmplitude M blank m n ≤
      (1/2 : ℝ)^n := by
  apply (mul_le_mul_of_nonneg_right (stageWire_card_growth_real M hM blank m n)
    (stageAmplitude_nonneg M blank m n)).trans
  have hF : (0 : ℝ) ≤ addressFactor M blank m := Nat.cast_nonneg _
  have hA : (1 : ℝ) ≤ addressGrowth M blank := by exact_mod_cast addressGrowth_ge_one M blank
  simpa only [stageAmplitude, workFactor, workGrowth, mul_div_assoc] using
    geometric_work_bound hF hA n

end ForcedComputation.ExpandingDetector

end

end OAI
