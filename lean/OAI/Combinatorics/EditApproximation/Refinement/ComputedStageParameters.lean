import OAI.Combinatorics.EditApproximation.Refinement.StageParameterBounds
import OAI.Combinatorics.EditApproximation.Geometry.TreeParameters

namespace OAI

/-! Numerical premises for the computed physical refinement stage. -/

namespace EditApproximation

 theorem computed_stage_grid_bounds (N : ℕ) (hN : 0 < N) :
    66 ≤ (integerParameters N).P ∧
      (800 * (inputHeight N : ℝ) ^ 2) ≤ (integerParameters N).P ∧
      4 * ((integerParameters N).M : ℝ) / (integerParameters N).P ≤ 1 := by
  let H := inputHeight N
  let P := (integerParameters N).P
  let M := (integerParameters N).M
  have hHtwo : 2 ≤ H := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (heightExponent_pos N hN)
    simpa only [H, inputHeight, pow_one] using h
  have hHone : 1 ≤ H := by omega
  have hM : M ≤ H := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hH18 : 800 ≤ H ^ 18 := by
    have h := Nat.pow_le_pow_left hHtwo 18
    norm_num only [show (2 : ℕ) ^ 18 = 262144 by norm_num] at h
    omega
  have hP20 : H ^ 20 ≤ P := pow_le_pow_right₀ hHone (by omega : 20 ≤ coarseExponent (inputSmallLog N) + 20)
  have hP800 : 800 * H ^ 2 ≤ P := by
    calc
      800 * H ^ 2 ≤ H ^ 18 * H ^ 2 := Nat.mul_le_mul_right _ hH18
      _ = H ^ 20 := by rw [← pow_add]
      _ ≤ P := hP20
  have hHP : (800 * (H : ℝ) ^ 2) ≤ P := by exact_mod_cast hP800
  have hP66 : 66 ≤ P := by
    have h : 4 ≤ H ^ 2 := by nlinarith only [hHtwo]
    nlinarith only [hP800, h]
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hHtwo
  have hMr : (M : ℝ) ≤ H := by exact_mod_cast hM
  refine ⟨hP66, hHP, ?_⟩
  apply (div_le_one₀ hPr).2
  nlinarith only [hHP, hHr, hMr]

 theorem computed_stage_tree_small (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    (intervalTreeDepth (integerParameters N).M nx : ℝ) *
      (4 * ((integerParameters N).M : ℝ) / (integerParameters N).P) ≤ 1 / 2 := by
  let H := inputHeight N
  let M := (integerParameters N).M
  let P := (integerParameters N).P
  let J := intervalTreeDepth M nx
  have hdepth := computed_tree_depth_bound N nx hN hnx hell
  have hellone : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
  have hJ : J ≤ 100 * H := by
    calc
      J = J * 1 := (Nat.mul_one J).symm
      _ ≤ J * inputSmallLog N := Nat.mul_le_mul_left J hellone
      _ ≤ 100 * H := hdepth
  have hJR : (J : ℝ) ≤ 100 * H := by exact_mod_cast hJ
  have hM : M ≤ H := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hMR : (M : ℝ) ≤ H := by exact_mod_cast hM
  have hP800 := (computed_stage_grid_bounds N hN).2.1
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P from lt_of_lt_of_le (by decide) (computed_stage_grid_bounds N hN).1)
  have hproduct := mul_le_mul hJR hMR (Nat.cast_nonneg M) (by positivity : (0 : ℝ) ≤ 100 * H)
  change (J : ℝ) * (4 * (M : ℝ) / P) ≤ _
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hPr).2
  nlinarith only [hproduct, hP800]

 theorem computed_stage_positive_counts (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    0 < (integerParameters N).T ∧ 0 < (integerParameters N).S := by
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast (Nat.one_le_two_pow (n := smallLogExponent N))
  have hpow := (pow_le_pow_right₀ hellone (by decide : 2 ≤ 20000)).trans (inputHeight_polynomial_slack N hN hell)
  have hpowN : inputSmallLog N ^ 2 ≤ inputHeight N := by exact_mod_cast hpow
  have hellpos : 0 < inputSmallLog N := Nat.two_pow_pos _
  exact ⟨Nat.two_pow_pos _, Nat.div_pos hpowN (pow_pos hellpos 2)⟩

end EditApproximation

end OAI
