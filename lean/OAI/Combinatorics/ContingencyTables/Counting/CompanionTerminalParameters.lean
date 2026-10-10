import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace OAI

/-! # The companion's literal terminal parameter choices -/

namespace ContingencyTables.CompanionTerminalParameters

noncomputable def precision (epsilon : ℝ) : ℕ := Nat.ceil (Real.logb 2 (1/epsilon))

noncomputable def allowance (L d : ℕ) (epsilon : ℝ) : ℕ :=
  20*(L+d+precision epsilon+1)

noncomputable def gamma (L d : ℕ) (epsilon : ℝ) : ℝ :=
  epsilon/(512*(d:ℝ)*allowance L d epsilon)

noncomputable def coefficient (L d : ℕ) (epsilon : ℝ) : ℕ :=
  Nat.ceil (4*(allowance L d epsilon:ℝ)/gamma L d epsilon)

lemma allowance_positive (L d : ℕ) (epsilon : ℝ) : 0 < allowance L d epsilon := by
  unfold allowance
  omega

lemma allowance_bits (L d : ℕ) (epsilon : ℝ) : 2*L ≤ allowance L d epsilon := by
  unfold allowance
  omega

lemma gamma_positive (L d : ℕ) (epsilon : ℝ) (hd : 1 ≤ d) (he : 0 < epsilon) :
    0 < gamma L d epsilon := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hK : (0:ℝ) < allowance L d epsilon := by exact_mod_cast allowance_positive L d epsilon
  unfold gamma
  positivity

lemma gamma_le_one (L d : ℕ) (epsilon : ℝ) (hd : 1 ≤ d)
    (he1 : epsilon < 1) : gamma L d epsilon ≤ 1 := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (1:ℝ) ≤ allowance L d epsilon := by
    exact_mod_cast (show 1 ≤ allowance L d epsilon from allowance_positive L d epsilon)
  unfold gamma
  apply (div_le_one (by positivity)).mpr
  nlinarith [mul_le_mul hdR hKR (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ d)]

lemma near_fraction (L d : ℕ) (epsilon : ℝ) (hd : 1 ≤ d) :
    4*(d:ℝ)*gamma L d epsilon*allowance L d epsilon=epsilon/128 := by
  have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hK0 : (allowance L d epsilon:ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (allowance_positive L d epsilon))
  unfold gamma
  field_simp [hd0,hK0]
  ring

lemma coefficient_positive (L d : ℕ) (epsilon : ℝ) (hd : 1 ≤ d) (he : 0 < epsilon) :
    0 < coefficient L d epsilon := by
  apply Nat.one_le_ceil_iff.mpr
  have hK : (0:ℝ) < allowance L d epsilon := by exact_mod_cast allowance_positive L d epsilon
  exact div_pos (by positivity) (gamma_positive L d epsilon hd he)

lemma terminal_scale (L d : ℕ) (epsilon : ℝ) (hd : 1 ≤ d) (he : 0 < epsilon) :
    4*(allowance L d epsilon:ℝ) ≤ (coefficient L d epsilon:ℝ)*gamma L d epsilon := by
  have hg := gamma_positive L d epsilon hd he
  have hh := mul_le_mul_of_nonneg_right
    (Nat.le_ceil (4*(allowance L d epsilon:ℝ)/gamma L d epsilon)) hg.le
  rw [div_mul_cancel₀ _ hg.ne'] at hh
  exact hh

lemma reciprocal_precision (epsilon : ℝ) (he : 0 < epsilon) :
    (2:ℝ)^(-(precision epsilon:ℝ)) ≤ epsilon := by
  have hq : 1/epsilon ≤ (2:ℝ)^(precision epsilon:ℝ) := by
    calc
      _ = (2:ℝ)^Real.logb 2 (1/epsilon) :=
        (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),← one_div]
  have hh := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 1/epsilon) hq
  simpa using hh

lemma far_fraction (L d : ℕ) (epsilon : ℝ) (he : 0 < epsilon) :
    (2:ℝ)^(-(3*allowance L d epsilon:ℕ):ℝ) ≤ epsilon/128 := by
  have hindex : precision epsilon+7 ≤ 3*allowance L d epsilon := by
    unfold allowance
    omega
  calc
    _ ≤ (2:ℝ)^(-((precision epsilon:ℝ)+7)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast (show
        -((3*allowance L d epsilon:ℕ):ℤ) ≤ -((precision epsilon+7:ℕ):ℤ) by omega))
    _ = (2:ℝ)^(-(precision epsilon:ℝ))/128 := by
      rw [neg_add,Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      norm_num; ring
    _ ≤ _ := div_le_div_of_nonneg_right (reciprocal_precision epsilon he) (by norm_num)

end ContingencyTables.CompanionTerminalParameters

end OAI
