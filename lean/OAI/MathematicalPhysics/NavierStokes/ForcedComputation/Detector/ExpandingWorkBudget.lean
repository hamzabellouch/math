import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateCount
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingDetectorScales

namespace OAI

/-! A computable choice of schedule pays for the product of the number
of gates and the largest address. This is the arithmetic part of the
global derivative bound. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open Recorder

def workGrowth (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) : ℝ :=
  2 * (addressGrowth M blank : ℝ) ^ 2

def workFactor (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ) : ℝ :=
  9 * ((addressFactor M blank m : ℝ) + 1) ^ 2

theorem workGrowth_ge_one (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) : 1 ≤ workGrowth M blank := by
  have hA : (1 : ℝ) ≤ addressGrowth M blank := by exact_mod_cast addressGrowth_ge_one M blank
  unfold workGrowth
  nlinarith

theorem workFactor_nonneg (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ) :
    0 ≤ workFactor M blank m := by unfold workFactor; positivity

theorem geometric_work_bound {F A : ℝ} (hF : 0 ≤ F) (hA : 1 ≤ A) (n : ℕ) :
    (F * A ^ n) * (F * A ^ (n + 1) + 2) /
      (9 * (F + 1) ^ 2 * (2 * A ^ 2) ^ (n + 1) + 2) ≤ (1 / 2 : ℝ) ^ n := by
  let b := (F + 1) * A ^ (n + 1)
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hpow : 1 ≤ A ^ (n + 1) := one_le_pow₀ hA
  have hb : 1 ≤ b := by dsimp [b]; nlinarith
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hgrow : A ^ n ≤ A ^ (n + 1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg hAp.le n) hA
  have hn : F * A ^ n ≤ b := by
    dsimp [b]
    exact mul_le_mul (by linarith : F ≤ F + 1) hgrow (pow_nonneg hAp.le n) (by linarith)
  have ha : F * A ^ (n + 1) + 2 ≤ 3 * b := by dsimp [b] at *; nlinarith
  have hnum : (F * A ^ n) * (F * A ^ (n + 1) + 2) ≤ 3 * b ^ 2 := by
    have hh := mul_le_mul hn ha (by positivity : 0 ≤ F * A ^ (n + 1) + 2) hb0.le
    nlinarith
  have he : 9 * (F + 1) ^ 2 * (2 * A ^ 2) ^ (n + 1) = 9 * b ^ 2 * 2 ^ (n + 1) := by
    dsimp [b]
    simp only [mul_pow, ← pow_mul]
    rw [Nat.mul_comm 2 (n + 1)]
    ring
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < 9 * b ^ 2 * 2 ^ (n + 1) + 2)).mpr
  have hp : (1 / 2 : ℝ) ^ n * 2 ^ (n + 1) = 2 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num
  have hh : (1 / 2 : ℝ) ^ n * (9 * b ^ 2 * 2 ^ (n + 1)) = 18 * b ^ 2 := by
    calc
      _ = 9 * b ^ 2 * ((1 / 2 : ℝ) ^ n * 2 ^ (n + 1)) := by ring
      _ = _ := by rw [hp]; ring
  have hpn : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  nlinarith [sq_nonneg b]

end ForcedComputation.ExpandingDetector

end

end OAI
