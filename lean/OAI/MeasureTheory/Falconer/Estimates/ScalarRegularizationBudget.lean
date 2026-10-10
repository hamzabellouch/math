import OAI.MeasureTheory.Falconer.Estimates.ScalarBinaryParameters

namespace OAI

/-! A square parameter absorbs the logarithmic loss of the initial
 scalar regularization. -/
namespace Falconer

 theorem scalar_square_dominates_linear {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∃ n : ℕ, 5 ≤ n ∧ β+4*(n:ℝ) ≤ α*(n:ℝ)^2 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 5 ((β+4)/α))
  have hn5 : (5:ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn1 : (1:ℝ) ≤ n := by linarith
  have hn0 : (0:ℝ) ≤ n := by positivity
  have hmul : β+4 ≤ α*(n:ℝ) := by
    simpa only [mul_comm] using
      (le_of_lt ((div_lt_iff₀ hα).1 ((le_max_right _ _).trans_lt hn)))
  have hm := mul_le_mul_of_nonneg_right hmul hn0
  have hb := mul_le_mul_of_nonneg_left hn1 hβ
  refine ⟨n,by exact_mod_cast (show (5:ℝ) ≤ n by linarith),?_⟩
  nlinarith

 theorem scalar_regularization_log_bound (D n : ℕ) (hn : 1 ≤ n) :
    Real.log (2050*((D^2*n^2)+1)^2:ℝ) ≤
      Real.log 2050+2*Real.log ((D:ℝ)^2+1)+4*(n:ℝ) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hn2 : (1:ℝ) ≤ (n:ℝ)^2 := by nlinarith
  have hp : (D:ℝ)^2*(n:ℝ)^2+1 ≤ ((D:ℝ)^2+1)*(n:ℝ)^2 := by nlinarith
  have hl := Real.log_le_log (by positivity : (0:ℝ) < (D:ℝ)^2*(n:ℝ)^2+1) hp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hl
  have hnlog := Real.log_le_sub_one_of_pos hn0
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
  norm_num only [Nat.cast_ofNat] at hl ⊢
  nlinarith

end Falconer

end OAI
