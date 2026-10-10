import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.RichParameters

lemma pair_exp_bound {N M J : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N)
    (hpack : J * (M*(M-1)) ≤ N^2) :
    (J:ℝ)*Real.exp (-(256/3:ℝ)*Real.sqrt ((N:ℝ)/M)) < 1/2 := by
  have hMp : (0:ℝ) < M := by exact_mod_cast lt_of_lt_of_le (by decide : 0<2) hM
  have hM2 : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hN : (M:ℝ) ≤ N := by exact_mod_cast hMN
  have hpack' : (J:ℝ)*((M:ℝ)*(M-1)) ≤ (N:ℝ)^2 := by
    have H := (Nat.cast_le (α := ℝ)).mpr hpack
    push_cast [Nat.cast_sub (show 1 ≤ M by omega)] at H
    exact H
  let r := Real.sqrt ((N:ℝ)/M)
  have hr : 1 ≤ r := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    simpa using (le_div_iff₀ hMp).mpr (by simpa using hN)
  have hrsq : r^2 = (N:ℝ)/M := Real.sq_sqrt (by positivity)
  have hrN : r^2*M = N := by rw [hrsq, div_mul_cancel₀ _ (ne_of_gt hMp)]
  have hJM : (J:ℝ)*(M:ℝ)^2 ≤ 2*(N:ℝ)^2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ J by positivity) (show (0:ℝ) ≤ M*(M-2) by positivity)]
  have hJ : (J:ℝ) ≤ 2*r^4 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hMp)).mp
    nlinarith [sq_nonneg (r^2*M-(N:ℝ)), sq_nonneg (r^2*M+(N:ℝ))]
  have hre : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have hre4 : r^4 ≤ Real.exp (4*r) := by
    rw [show (4:ℝ)*r = (4:ℕ)*r by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hre 4
  have hsmall : Real.exp (-2) < (1/4:ℝ) := by
    have he : (2:ℝ) < Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)
    have he2 : (4:ℝ) < Real.exp 2 := by
      calc
        (4:ℝ) < (Real.exp 1)^2 := by nlinarith [Real.exp_pos (1:ℝ)]
        _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [Real.exp_neg]
    rw [← one_div]
    exact (div_lt_div_iff_of_pos_left (by norm_num) (Real.exp_pos _) (by norm_num)).mpr he2
  calc
    (J:ℝ)*Real.exp (-(256/3:ℝ)*r) ≤ 2*r^4*Real.exp (-(256/3:ℝ)*r) :=
      mul_le_mul_of_nonneg_right hJ (Real.exp_pos _).le
    _ ≤ 2*Real.exp (4*r)*Real.exp (-(256/3:ℝ)*r) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hre4 (by norm_num)) (Real.exp_pos _).le
    _ = 2*Real.exp (4*r-(256/3:ℝ)*r) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ 2*Real.exp (-2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      linarith
    _ < 1/2 := by linarith
end SharpRamseyFive.RichParameters

end OAI
