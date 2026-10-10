import OAI.Combinatorics.EditApproximation.Coarse.CoarseParameters
import OAI.Combinatorics.EditApproximation.Geometry.TreeParameters

namespace OAI

/-! The computed parameters discharge the comparison-tree small-growth premises. -/

namespace EditApproximation

theorem computed_comparison_parameters (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    66 ≤ (integerParameters N).P ∧
      (intervalTreeDepth (integerParameters N).M nx : ℝ) *
        (4 * ((integerParameters N).M : ℝ) / (integerParameters N).P) ≤ 1 / 2 := by
  let H := inputHeight N
  let M := (integerParameters N).M
  let J := intervalTreeDepth M nx
  let P := (integerParameters N).P
  have hH : 4 ≤ H := (computed_coarse_branching N hN hell).1
  have hM : M ≤ H := by
    exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hMtwo : 2 ≤ M := (computed_branching_bounds N hN hell).1
  have hJ : J ≤ H := by
    have hlog := Nat.clog_anti_left (by decide : 1 < 2) hMtwo (n := max 1 nx)
    have hlength : max 1 nx ≤ 2 ^ H := by
      apply max_le Nat.one_le_two_pow
      exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
    exact hlog.trans ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hlength)
  have hPfour : H ^ 4 ≤ P :=
    pow_le_pow_right₀ (by omega : 1 ≤ H) (by omega : 4 ≤ coarseExponent (inputSmallLog N) + 20)
  have hHsq : 16 ≤ H ^ 2 := by nlinarith
  have hHfour : 256 ≤ H ^ 4 := by
    have h := Nat.pow_le_pow_left hH 4
    norm_num at h
    exact h
  have h66 : 66 ≤ P := by omega
  have hprod : M * J ≤ H ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hM hJ
  have hscale : 8 * M * J ≤ P := by
    have hmul := Nat.mul_le_mul_left (H ^ 2) hHsq
    nlinarith
  have hPr : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hscaleR : 8 * (M : ℝ) * J ≤ P := by exact_mod_cast hscale
  refine ⟨h66, ?_⟩
  change (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hPr).2
  nlinarith

end EditApproximation

end OAI
