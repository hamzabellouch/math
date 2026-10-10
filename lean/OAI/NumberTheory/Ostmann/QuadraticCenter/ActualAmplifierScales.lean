import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifierWeight
import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterSelectionSize

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_prime_band_le_sqrt_parameterX :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ, Real.log Z ≤ 2*T →
      (Z : ℝ) ≤ Real.sqrt (parameterX T : ℝ) := by
  filter_upwards [eventually_parameterX_log_bounds,
    eventually_mul_rpow_le_rpow 8 (a := 1) (b := 8/5) (by norm_num)] with T hX hg
  intro Z hZ
  by_cases hz : Z=0
  · simp [hz]
  have hzp : (0:ℝ)<Z := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hxp : (0:ℝ)<parameterX T := by
    have hlogp : 0 < Real.log (parameterX T:ℝ) := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hX.2.1
    have hh := (Real.log_pos_iff (Nat.cast_nonneg (parameterX T))).mp hlogp
    linarith
  apply (Real.log_le_log_iff hzp (Real.sqrt_pos.mpr hxp)).mp
  rw [Real.log_sqrt hxp.le]
  rw [Real.rpow_one] at hg
  linarith [hX.2.2.1]

theorem auxiliary_product_mass_scale {X Z L : ℕ} (hX : 1 ≤ X) (hZ : 1 ≤ Z)
    (hL : 0 < L) (hZX : (Z:ℝ) ≤ Real.sqrt (X:ℝ))
    (hprod : (L:ℝ) ≤ (Z:ℝ) ^ (1/50:ℝ)) :
    (1/4:ℝ) ≤ (X:ℝ)/L := by
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hZr : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  have hsmall := Real.rpow_le_self_of_one_le hZr (by norm_num : (1/50:ℝ) ≤ 1)
  have hsqrt : Real.sqrt (X:ℝ) ≤ X := Real.sqrt_le_self_iff.mpr (Or.inr hXr)
  apply (le_div_iff₀ hLp).mpr
  linarith [hprod.trans (hsmall.trans (hZX.trans hsqrt))]

end Ostmann.QuadraticCenter

end

end OAI
