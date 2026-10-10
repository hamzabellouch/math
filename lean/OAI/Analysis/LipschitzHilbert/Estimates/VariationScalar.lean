import OAI.Analysis.LipschitzHilbert.Estimates.VariationPerturbation

namespace OAI

/-! Exact behavior of finite interval-sum variation under a common scalar.
This keeps polynomial localization independent of the number of scales. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem finiteCubicVariation_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (F : ℕ → E) (N : ℕ) :
    finiteCubicVariation (fun i => c • F i) N = |c| ^ 3 * finiteCubicVariation F N := by
  classical
  unfold finiteCubicVariation
  rw [Finset.mul₀_sup' (pow_nonneg (abs_nonneg c) 3)]
  congr 1
  funext p
  split_ifs with hp
  · simp only [← smul_sub, norm_smul, Real.norm_eq_abs, mul_pow, Finset.mul_sum]
  · exact (mul_zero _).symm

theorem finiteCubicVariation_smul_square {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (F : ℕ → E) (N : ℕ) :
    (finiteCubicVariation (fun i => c • F i) N) ^ (2 / 3 : ℝ) =
      c ^ 2 * (finiteCubicVariation F N) ^ (2 / 3 : ℝ) := by
  rw [finiteCubicVariation_smul, Real.mul_rpow (pow_nonneg (abs_nonneg c) 3)
    (finiteCubicVariation_nonneg F N)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg c)]
  norm_num [sq_abs]

theorem ennreal_finiteCubicVariation_smul_square {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (F : ℕ → E) (N : ℕ) :
    ENNReal.ofReal (finiteCubicVariation (fun i => c • F i) N) ^ (2 / 3 : ℝ) =
      ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (finiteCubicVariation F N) ^ (2 / 3 : ℝ) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num),
    finiteCubicVariation_smul_square, ENNReal.ofReal_mul (sq_nonneg c),
    ← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)]

end LipschitzHilbert

end

end OAI
