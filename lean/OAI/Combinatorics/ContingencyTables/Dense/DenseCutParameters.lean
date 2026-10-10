import OAI.Combinatorics.ContingencyTables.Dense.DenseScales
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! # Numerical interpolation parameters of the dense bin chain -/

namespace ContingencyTables.GridBoundary

noncomputable def denseInterpolation (d K : ℕ) : ℝ := 1 / (4 * (d : ℝ) * K)

theorem denseInterpolation_bounds (d K q : ℕ) (hd : 14 ≤ d) (hK : 1 ≤ K) (hq : q ≤ d) :
    0 < denseInterpolation d K ∧ denseInterpolation d K < 1 ∧
      denseInterpolation d K * K ≤ 1 / 4 ∧
      (q - 1 : ℕ) * (2 * (denseInterpolation d K * K)) ≤ (1 / 2 : ℝ) := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hK₁ : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have heq : denseInterpolation d K * K = 1 / (4 * (d : ℝ)) := by
    unfold denseInterpolation
    field_simp
  refine ⟨by unfold denseInterpolation; positivity, ?_, ?_, ?_⟩
  · unfold denseInterpolation
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  · rw [heq]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  · rw [heq]
    have hqd : ((q - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.sub_le q 1).trans hq
    calc
      _ ≤ (d : ℝ) * (2 * (1 / (4 * (d : ℝ)))) := by gcongr
      _ = 1 / 2 := by field_simp; ring

theorem two_rpow_gain (t : ℝ) (ht : 0 ≤ t) : t / 2 ≤ (2 : ℝ) ^ t - 1 := by
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hl
  have he := Real.add_one_le_exp (Real.log 2 * t)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [mul_le_mul_of_nonneg_right hl ht]

end ContingencyTables.GridBoundary

end OAI
