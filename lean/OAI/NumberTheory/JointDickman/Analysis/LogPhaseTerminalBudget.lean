import OAI.NumberTheory.JointDickman.Analysis.LogPhaseScale

namespace OAI

/-! # Scalar bounds for logarithmic terminal sums

These two elementary real inequalities are reused from the frozen internal
reciprocal-phase proof, with their names changed to the present application.
-/
namespace JointDickman

theorem logarithmic_terminal_error_bound {U a b Λ : ℝ} (hU : 1 ≤ U)
    (ha : 0 < a) (hb : 0 ≤ b)
    (hlower : a * U ^ (-(3 : ℝ) / 2) ≤ Λ)
    (hupper : Λ ≤ b * U ^ (-(2 : ℝ) / 5)) :
    U * Λ ^ ((1 : ℝ) / 2) + Λ ^ (-(1 : ℝ) / 2) + 1 ≤
      (b ^ ((1 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) + 1) * U ^ ((4 : ℝ) / 5) := by
  have hU0 : 0 < U := by linarith
  have hΛ : 0 < Λ := (mul_pos ha (Real.rpow_pos_of_pos hU0 _)).trans_le hlower
  have hroot := Real.rpow_le_rpow hΛ.le hupper (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [Real.mul_rpow hb (by positivity), ← Real.rpow_mul hU0.le] at hroot
  norm_num at hroot
  have hfirst : U * Λ ^ ((1 : ℝ) / 2) ≤ b ^ ((1 : ℝ) / 2) * U ^ ((4 : ℝ) / 5) := by
    calc
      U * Λ ^ ((1 : ℝ) / 2) ≤ U * (b ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left (by simpa only [neg_div] using hroot) hU0.le
      _ = b ^ ((1 : ℝ) / 2) * U ^ ((4 : ℝ) / 5) := by
        rw [mul_left_comm]
        congr 1
        calc
          U * U ^ (-(1 : ℝ) / 5) = U ^ (1 : ℝ) * U ^ (-(1 : ℝ) / 5) := by rw [Real.rpow_one]
          _ = U ^ ((1 : ℝ) + -(1 : ℝ) / 5) := (Real.rpow_add hU0 _ _).symm
          _ = U ^ ((4 : ℝ) / 5) := by norm_num
  have hinv := Real.rpow_le_rpow_of_nonpos
    (mul_pos ha (Real.rpow_pos_of_pos hU0 _)) hlower
    (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
  rw [Real.mul_rpow ha.le (by positivity), ← Real.rpow_mul hU0.le] at hinv
  norm_num at hinv
  have hsecond : Λ ^ (-(1 : ℝ) / 2) ≤ a ^ (-(1 : ℝ) / 2) * U ^ ((4 : ℝ) / 5) := by
    simpa only [neg_div] using hinv.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU (by norm_num : (3 : ℝ) / 4 ≤ 4 / 5)) (by positivity))
  have hone : 1 ≤ U ^ ((4 : ℝ) / 5) := Real.one_le_rpow hU (by norm_num)
  nlinarith


theorem logarithmic_terminal_sqrt_budget {U a lam T : ℝ} (hU : 1 ≤ U)
    (ha : 0 < a) (hT : T ≤ 3 * U)
    (hlower : a * U ^ (-(3 : ℝ) / 2) ≤ lam)
    (hupper : lam ≤ a * U ^ (-(2 : ℝ) / 5)) :
    T * Real.sqrt lam + 1 / Real.sqrt lam ≤
      3 * (a ^ ((1 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) + 1) * U ^ ((4 : ℝ) / 5) := by
  have hlam : 0 < lam := (mul_pos ha (Real.rpow_pos_of_pos (by linarith) _)).trans_le hlower
  have h := logarithmic_terminal_error_bound hU ha ha.le hlower hupper
  have hinv : lam ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt lam := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hlam.le, ← Real.sqrt_eq_rpow, one_div]
  rw [← Real.sqrt_eq_rpow, hinv] at h
  have hs := mul_le_mul_of_nonneg_right hT (Real.sqrt_nonneg lam)
  have hi : 0 ≤ 1 / Real.sqrt lam := by positivity
  nlinarith


end JointDickman

end OAI
