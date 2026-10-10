import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateExternal
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Filter InitialCharacterScale

theorem code_matching_harmonic_gain (r m : ℕ) (L z : ℝ)
    (hL : 0<L) (hz : 0<z) (hm : (m:ℝ)≤z*L) :
    (2*(m:ℝ))^(r*m)*L^(-((r*m:ℕ):ℝ)) ≤
      Real.exp (((r*m:ℕ):ℝ)*(Real.log z+Real.log 2)) := by
  have hratio : 2*(m:ℝ)/L≤2*z := (div_le_iff₀ hL).mpr (by linarith)
  rw [Real.rpow_neg hL.le,Real.rpow_natCast,←div_eq_mul_inv,←div_pow]
  calc
    _ ≤ (2*z)^(r*m) := pow_le_pow_left₀ (div_nonneg (by positivity) hL.le) hratio _
    _ = _ := by
      have hp : 0<2*z := by positivity
      conv_lhs => rw [←Real.exp_log hp]
      rw [←Real.exp_nat_mul,Real.log_mul (by norm_num : (2:ℝ)≠0) hz.ne']
      congr 1
      ring

theorem code_preserving_scalar_bound (r m : ℕ) (L z C D A ε Δ W F : ℝ)
    (hL : 0<L) (hz : 0<z) (hm : (m:ℝ)≤z*L) :
    (2*(m:ℝ))^(r*m)*(L^(-((r*m:ℕ):ℝ))*Real.exp (C*((r*m:ℕ):ℝ)+D))*
      Real.exp (-Δ+W)*Real.exp (A*(r:ℝ)*L+ε*m)*Real.exp F ≤
      Real.exp (-Δ+((r*m:ℕ):ℝ)*(Real.log z+C+Real.log 2)+A*r*L+ε*m+D+W+F) := by
  calc
    _ = ((2*(m:ℝ))^(r*m)*L^(-((r*m:ℕ):ℝ)))*
        (Real.exp (C*((r*m:ℕ):ℝ)+D)*Real.exp (-Δ+W)*
          Real.exp (A*(r:ℝ)*L+ε*m)*Real.exp F) := by ring
    _ ≤ Real.exp (((r*m:ℕ):ℝ)*(Real.log z+Real.log 2))*
        (Real.exp (C*((r*m:ℕ):ℝ)+D)*Real.exp (-Δ+W)*
          Real.exp (A*(r:ℝ)*L+ε*m)*Real.exp F) :=
      mul_le_mul_of_nonneg_right (code_matching_harmonic_gain r m L z hL hz hm) (by positivity)
    _ = _ := by
      simp only [←Real.exp_add]
      congr 1
      ring

theorem actual_code_matching_harmonic_gain (k j : ℕ) {L : ℝ} (hL : 0<L) :
    (2*(wordSize k L:ℝ))^(2^j*wordSize k L)*
      L^(-((2^j*wordSize k L:ℕ):ℝ)) ≤
      Real.exp (((2^j*wordSize k L:ℕ):ℝ)*(Real.log (depthScale k)+Real.log 2)) :=
  code_matching_harmonic_gain _ _ L (depthScale k) hL (depthScale_pos k)
    (wordSize_bounds k hL.le).2

end Ostmann.Characters.DiagonalEstimate

end

end OAI
