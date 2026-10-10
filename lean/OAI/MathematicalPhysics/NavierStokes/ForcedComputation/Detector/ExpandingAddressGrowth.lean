import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingFiniteGraph

namespace OAI

/-! Explicit exponential address bounds supply the two computable
parameters in the expanding schedule. -/

namespace ForcedComputation.ExpandingDetector
open Recorder

def addressGrowth (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) : ℕ := alphabetBase M blank ^ 2

def addressFactor (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ) : ℕ :=
  (allControls M).length * addressGrowth M blank ^ m

theorem addressGrowth_ge_one (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) : 1 ≤ addressGrowth M blank := by
  have hb := alphabetBase_two_le M blank
  unfold addressGrowth
  nlinarith

theorem address_number_growth (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m n : ℕ)
    (a : RecorderAddress M blank (m + n)) :
    a.number ≤ addressFactor M blank m * addressGrowth M blank ^ n := by
  calc
    a.number ≤ (allControls M).length * (alphabetBase M blank ^ (m + n)) ^ 2 :=
      a.number_bounds.2
    _ = _ := by
      unfold addressFactor addressGrowth
      have hm : (alphabetBase M blank ^ m) ^ 2 = (alphabetBase M blank ^ 2) ^ m := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm m 2]
      have hn : (alphabetBase M blank ^ n) ^ 2 = (alphabetBase M blank ^ 2) ^ n := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
      simp only [pow_add, mul_pow, hm, hn]
      ring

theorem address_number_growth_real (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m n : ℕ)
    (a : RecorderAddress M blank (m + n)) :
    (a.number : ℝ) ≤ (addressFactor M blank m : ℝ) * (addressGrowth M blank : ℝ) ^ n := by
  exact_mod_cast address_number_growth M blank m n a

end ForcedComputation.ExpandingDetector

end OAI
