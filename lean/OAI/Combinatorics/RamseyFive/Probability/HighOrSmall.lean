import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

theorem high_or_small {q n a : ℝ} (_hq : 0 ≤ q) (_hn : 0 < n) (ha : 0 ≤ a)
    (hhigh : 8388608*q^2 ≤ n) :
    2097152*q^2 ≤ n*a^2 ∨ n*a^99 ≤ q^2 := by
  by_cases h : 2097152*q^2 ≤ n*a^2
  · exact Or.inl h
  right
  have hlt : n*a^2 < 2097152*q^2 := lt_of_not_ge h
  have ha2 : a^2 < (1/2:ℝ)^2 := by
    have := mul_le_mul_of_nonneg_right hhigh (sq_nonneg a)
    nlinarith
  have ha' : a ≤ 1/2 := by nlinarith
  have hp := pow_le_pow_left₀ ha ha' 97
  calc
    n*a^99 = (n*a^2)*a^97 := by ring
    _ ≤ (2097152*q^2)*(1/2:ℝ)^97 := mul_le_mul hlt.le hp (pow_nonneg ha 97) (by positivity)
    _ ≤ q^2 := by
      have hc : (2097152:ℝ)*(1/2:ℝ)^97 ≤ 1 := by norm_num
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg q)]

end SharpRamseyFive.ScoreScalars

end OAI
