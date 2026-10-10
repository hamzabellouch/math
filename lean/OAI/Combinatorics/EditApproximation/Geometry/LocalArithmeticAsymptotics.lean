import OAI.Combinatorics.EditApproximation.Geometry.LocalArithmeticBudget
import OAI.Combinatorics.EditApproximation.Geometry.DependencyPathEnvelope
import OAI.Combinatorics.EditApproximation.Geometry.SubexponentialTransfer

namespace OAI

/-! The actual finite optimizer arithmetic counter is subpolynomial in the
input length. This statement does not include the separate bit-operation
and local-data preparation counters. -/

namespace EditApproximation

open Filter
open scoped Topology

noncomputable def computedLocalArithmeticExponent (N : ℕ) : ℝ :=
  Real.log 2 + (44 * Real.log 2) * ((integerParameters N).M : ℝ) *
    ((coarseExponent (inputSmallLog N) : ℝ) + 1) * inputSmallLog N +
      10000 * ((coarseExponent (inputSmallLog N) : ℝ) + 1) * Real.log (inputHeight N : ℝ)

theorem computedLocalArithmeticExponent_tendsto :
    Tendsto (fun N => computedLocalArithmeticExponent N / inputHeight N) atTop (𝓝 0) := by
  have hconstant : Tendsto (fun N => Real.log 2 / (inputHeight N : ℝ)) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, mul_zero, div_eq_mul_inv] using
      inputHeight_real_tendsto.inv_tendsto_atTop.const_mul (Real.log 2)
  have h := (hconstant.add (local_enumeration_exponent_div_height_tendsto.const_mul
    (44 * Real.log 2))).add (encoding_exponent_div_height_tendsto.const_mul 10000)
  simp only [zero_add, mul_zero] at h
  convert h using 1
  ext N
  unfold computedLocalArithmeticExponent
  ring

theorem computedLocalOptimizer_arithmetic_exp_bound (N : ℕ) (hN : 0 < N)
    (hH : 64 ≤ inputHeight N) :
    (localOptimizerArithmeticBudget (integerParameters N).M (integerParameters N).P
      (inputHeight N) : ℝ) ≤ Real.exp (computedLocalArithmeticExponent N) := by
  let H := inputHeight N
  let M := (integerParameters N).M
  let p := coarseExponent (inputSmallLog N)
  have hM : M ≤ H := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  have hP : 1 ≤ (integerParameters N).P := Nat.one_le_pow _ _ (by omega)
  have hbudget := localOptimizerArithmeticBudget_cap H M (integerParameters N).P p hH hM hP le_rfl
  have hbudgetR : (localOptimizerArithmeticBudget M (integerParameters N).P H : ℝ) ≤
      2 * (H : ℝ) ^ (44 * M * (p + 1)) * (H : ℝ) ^ (10000 * (p + 1)) := by
    exact_mod_cast hbudget
  have hlog : Real.log (H : ℝ) ≤ (inputSmallLog N : ℝ) * Real.log 2 := by
    rw [show H = inputHeight N from rfl, inputHeight_real_log]
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    exact_mod_cast (inputSmallLog_bounds N hN).1
  have hpow1 := nat_pow_eq_exp_log H (44 * M * (p + 1)) (by omega)
  have hpow2 := nat_pow_eq_exp_log H (10000 * (p + 1)) (by omega)
  change (localOptimizerArithmeticBudget M (integerParameters N).P H : ℝ) ≤ _
  calc
    _ ≤ 2 * (H : ℝ) ^ (44 * M * (p + 1)) * (H : ℝ) ^ (10000 * (p + 1)) := hbudgetR
    _ = Real.exp (Real.log 2 + (44 * M * (p + 1) : ℕ) * Real.log (H : ℝ) +
        (10000 * (p + 1) : ℕ) * Real.log (H : ℝ)) := by
      rw [hpow1, hpow2, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (computedLocalArithmeticExponent N) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hlog
        (Nat.cast_nonneg (44 * M * (p + 1)) : (0 : ℝ) ≤ (44 * M * (p + 1) : ℕ))
      push_cast at hmul ⊢
      unfold computedLocalArithmeticExponent
      dsimp only [M, p, H] at hmul ⊢
      nlinarith only [hmul]

theorem computedLocalOptimizer_arithmetic_subpolynomial (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop,
      (localOptimizerArithmeticBudget (integerParameters N).M (integerParameters N).P
        (inputHeight N) : ℝ) ≤ (N + 2 : ℝ) ^ epsilon := by
  filter_upwards [subexponential_height_to_input computedLocalArithmeticExponent
    computedLocalArithmeticExponent_tendsto epsilon hepsilon, eventually_ge_atTop 1,
    inputHeight_real_tendsto.eventually (eventually_ge_atTop 64)] with N hbound hN hH
  exact (computedLocalOptimizer_arithmetic_exp_bound N (by omega) (by exact_mod_cast hH)).trans hbound

end EditApproximation

end OAI
