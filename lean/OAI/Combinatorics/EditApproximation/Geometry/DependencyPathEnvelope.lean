import OAI.Combinatorics.EditApproximation.Geometry.SubexponentialTransfer
import OAI.Combinatorics.EditApproximation.Geometry.Work

namespace OAI

/-! An explicit subpolynomial envelope for the finite dependency-path sum.
The connection between this sum and an execution is a separate obligation. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem nat_pow_eq_exp_log (a n : ℕ) (ha : 0 < a) :
    (a : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log a) := by
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast ha)]

theorem dependencyPathBudget_exp_bound (M ell H q C₁ C₂ j K : ℕ)
    (hM : 1 ≤ M) (hell : 1 ≤ ell) (hH : 1 ≤ H) :
    (dependencyPathBudget j K (M * ell ^ C₁) (H ^ (C₂ * q)) : ℝ) ≤
      (M : ℝ) ^ j * Real.exp ((1 + Real.log 2) * (j + K : ℝ) +
        C₁ * j * Real.log (ell : ℝ) + C₂ * q * K * Real.log (H : ℝ)) := by
  have hsame : 1 ≤ M * ell ^ C₁ := by
    have hp : 1 ≤ ell ^ C₁ := one_le_pow₀ hell
    nlinarith
  have hearlier : 1 ≤ H ^ (C₂ * q) := one_le_pow₀ hH
  have hnat := dependencyPathBudget_le j K (M * ell ^ C₁) (H ^ (C₂ * q)) hsame hearlier
  have hcast : (dependencyPathBudget j K (M * ell ^ C₁) (H ^ (C₂ * q)) : ℝ) ≤
      (j + 1 : ℝ) * (K + 1 : ℝ) * (2 : ℝ) ^ (j + K) *
        ((M : ℝ) * (ell : ℝ) ^ C₁) ^ j * ((H : ℝ) ^ (C₂ * q)) ^ K := by
    exact_mod_cast hnat
  have hj : (j + 1 : ℝ) ≤ Real.exp (j : ℝ) := Real.add_one_le_exp _
  have hK : (K + 1 : ℝ) ≤ Real.exp (K : ℝ) := Real.add_one_le_exp _
  have hproduct : (j + 1 : ℝ) * (K + 1 : ℝ) ≤ Real.exp (j : ℝ) * Real.exp (K : ℝ) :=
    mul_le_mul hj hK (by positivity) (Real.exp_nonneg _)
  calc
    _ ≤ (j + 1 : ℝ) * (K + 1 : ℝ) * (2 : ℝ) ^ (j + K) *
        ((M : ℝ) * (ell : ℝ) ^ C₁) ^ j * ((H : ℝ) ^ (C₂ * q)) ^ K := hcast
    _ ≤ (Real.exp (j : ℝ) * Real.exp (K : ℝ)) * (2 : ℝ) ^ (j + K) *
        ((M : ℝ) * (ell : ℝ) ^ C₁) ^ j * ((H : ℝ) ^ (C₂ * q)) ^ K := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hproduct (by positivity)
    _ = (M : ℝ) ^ j * Real.exp ((1 + Real.log 2) * (j + K : ℝ) +
        C₁ * j * Real.log (ell : ℝ) + C₂ * q * K * Real.log (H : ℝ)) := by
      have htwo : (2 : ℝ) ^ (j + K) = Real.exp (((j + K : ℕ) : ℝ) * Real.log 2) := by
        simpa only [Nat.cast_ofNat] using nat_pow_eq_exp_log 2 (j + K) (by decide)
      rw [mul_pow, ← pow_mul, ← pow_mul, htwo,
        nat_pow_eq_exp_log ell (C₁ * j) (by omega),
        nat_pow_eq_exp_log H (C₂ * q * K) (by omega)]
      calc
        _ = (M : ℝ) ^ j * (Real.exp (j : ℝ) * Real.exp (K : ℝ) *
            Real.exp (((j + K : ℕ) : ℝ) * Real.log 2) *
            Real.exp (((C₁ * j : ℕ) : ℝ) * Real.log ell) *
            Real.exp (((C₂ * q * K : ℕ) : ℝ) * Real.log H)) := by ring
        _ = (M : ℝ) ^ j * Real.exp ((j : ℝ) + K +
            ((j + K : ℕ) : ℝ) * Real.log 2 + ((C₁ * j : ℕ) : ℝ) * Real.log ell +
            ((C₂ * q * K : ℕ) : ℝ) * Real.log H) := by simp only [← Real.exp_add]
        _ = _ := by congr 2; push_cast; ring

theorem computed_dependency_path_envelope (N C₁ C₂ j : ℕ)
    (hj : j ≤ computedMaxTreeDepth N) :
    (dependencyPathBudget j (computedDependencyIndexCount N)
      ((integerParameters N).M * inputSmallLog N ^ C₁)
      (inputHeight N ^ (C₂ * (coarseExponent (inputSmallLog N) + 1))) : ℝ) ≤
      ((integerParameters N).M : ℝ) ^ j *
        Real.exp (computedDependencyOverheadExponent C₁ C₂ N) := by
  have hM : 1 ≤ (integerParameters N).M := Nat.one_le_two_pow
  have hell : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
  have hH : 1 ≤ inputHeight N := Nat.one_le_two_pow
  have h := dependencyPathBudget_exp_bound (integerParameters N).M (inputSmallLog N)
    (inputHeight N) (coarseExponent (inputSmallLog N) + 1) C₁ C₂ j
    (computedDependencyIndexCount N) hM hell hH
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  unfold computedDependencyOverheadExponent
  have hjR : (j : ℝ) ≤ computedMaxTreeDepth N := by exact_mod_cast hj
  have hlog : 0 ≤ Real.log (inputSmallLog N : ℝ) := Real.log_nonneg (by exact_mod_cast hell)
  have hlogtwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hjR (mul_nonneg (Nat.cast_nonneg C₁) hlog)]

/-- The entire displayed path bound is `M^j` times a subpolynomial factor,
uniformly at all physical depths. -/
theorem computed_dependency_path_subpolynomial (C₁ C₂ : ℕ) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ j ≤ computedMaxTreeDepth N,
      (dependencyPathBudget j (computedDependencyIndexCount N)
        ((integerParameters N).M * inputSmallLog N ^ C₁)
        (inputHeight N ^ (C₂ * (coarseExponent (inputSmallLog N) + 1))) : ℝ) ≤
        ((integerParameters N).M : ℝ) ^ j * (N + 2 : ℝ) ^ epsilon := by
  filter_upwards [subexponential_height_to_input _
    (computedDependencyOverheadExponent_tendsto C₁ C₂) epsilon hepsilon] with N hN
  intro j hj
  exact (computed_dependency_path_envelope N C₁ C₂ j hj).trans
    (mul_le_mul_of_nonneg_left hN (by positivity))

end EditApproximation

end OAI
