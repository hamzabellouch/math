import OAI.Combinatorics.EditApproximation.Geometry.Parameters
import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitial
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Computed numerical premises of the initial seed

The literal dyadic estimator uses the input-computed branching factor,
threshold and precision. Its depth and distortion bounds follow from
those integer parameters.
-/

namespace EditApproximation





theorem computed_coarse_branching (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    4 ≤ inputHeight N ∧ inputHeight N ≤ (integerParameters N).B := by
  have hlogs := inputSmallLog_bounds N hN
  have hexp : 2 ≤ heightExponent N := by omega
  have hH : 4 ≤ inputHeight N := by
    change 2 ^ 2 ≤ 2 ^ heightExponent N
    exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hexp
  have hlog : 1 ^ 4 ≤ Nat.log 2 (inputSmallLog N) := by
    apply Nat.le_log_of_pow_le (by decide : 1 < 2)
    norm_num
    omega
  have hp := coarseExponent_maximal (inputSmallLog N) 1 hlog
  have hB : inputHeight N ≤ inputHeight N ^ coarseExponent (inputSmallLog N) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ inputHeight N) hp
  exact ⟨hH, hB⟩

theorem computed_coarse_depth (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    n ≤ (integerParameters N).B ^ computedCoarseDepth N n ∧
      computedCoarseDepth N n ≤ inputHeight N := by
  have hB := computed_coarse_branching N hN hell
  have hBtwo : 2 ≤ (integerParameters N).B := by omega
  constructor
  · exact (le_max_right 1 n).trans (Nat.le_pow_clog hBtwo (max 1 n))
  · have hanti := Nat.clog_anti_left (by decide : 1 < 2) hBtwo (n := max 1 n)
    have hlength : max 1 n ≤ 2 ^ inputHeight N := by
      apply max_le Nat.one_le_two_pow
      exact hn.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
    exact hanti.trans ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hlength)

theorem computed_coarse_structuralFactor (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    coarseStructuralFactor (initialLambda N) (computedCoarseDepth N n) ≤ 2 := by
  have hH := (computed_coarse_branching N hN hell).1
  have hHQ : (4 : ℚ) ≤ inputHeight N := by exact_mod_cast hH
  have hD : (computedCoarseDepth N n : ℚ) ≤ inputHeight N := by
    exact_mod_cast (computed_coarse_depth N n hN hn hell).2
  apply coarseStructuralFactor_le_two
  · unfold initialLambda
    positivity
  · unfold initialLambda
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 64 * inputHeight N)).2
    nlinarith
  · unfold initialLambda
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 64 * inputHeight N)).2
    nlinarith

theorem computed_coarse_distortion (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    25 + 16 * (integerParameters N).B * computedCoarseDepth N n ≤
      (integerParameters N).initialFactor := by
  let H := inputHeight N
  let B := (integerParameters N).B
  have hH : 4 ≤ H := (computed_coarse_branching N hN hell).1
  have hB : 1 ≤ B := by have h := (computed_coarse_branching N hN hell).2; omega
  have hD : computedCoarseDepth N n ≤ H := (computed_coarse_depth N n hN hn hell).2
  have hpoly : 25 + 16 * H ≤ H ^ 4 := by
    have hsq : 16 ≤ H ^ 2 := by nlinarith
    have hmul := Nat.mul_le_mul_left (H ^ 2) hsq
    nlinarith
  have hscaled := Nat.mul_le_mul_left B hpoly
  have hdepth := Nat.mul_le_mul_left (16 * B) hD
  have hfactor : (integerParameters N).initialFactor = B * H ^ 4 := by
    exact pow_add H (coarseExponent (inputSmallLog N)) 4
  rw [hfactor]
  nlinarith

end EditApproximation

end OAI
