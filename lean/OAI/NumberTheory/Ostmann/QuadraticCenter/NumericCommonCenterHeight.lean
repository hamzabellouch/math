import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericCommonCenterBasic
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericProductLift

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter

theorem quadraticLiftMultiplierBound_le (Z : ℕ) (hZ : 1 ≤ Z) :
    (quadraticLiftMultiplierBound Z : ℝ) ≤ 2 * (Z : ℝ)^(13/100:ℝ) := by
  have hZr : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hp := Real.one_le_rpow hZr (by norm_num : (0:ℝ)≤13/100)
  have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg Z) (13/100:ℝ))
  change (quadraticLiftMultiplierBound Z : ℝ) < (Z : ℝ)^(13/100:ℝ)+1 at hh
  linarith

theorem quadraticLiftHeight_le (X : ℝ) (Z : ℕ) (hX : 1 ≤ X) (hZ : 1 ≤ Z) :
    (quadraticLiftHeight X Z : ℝ) ≤ 2 * X * Z := by
  have hZr : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hpow := Real.rpow_le_self_of_one_le hZr (by norm_num : (13/100:ℝ)≤1)
  have hh := Nat.ceil_lt_add_one (show 0 ≤ X*(Z:ℝ)^(13/100:ℝ) by positivity)
  change (quadraticLiftHeight X Z : ℝ) < X*(Z:ℝ)^(13/100:ℝ)+1 at hh
  have hm := mul_le_mul_of_nonneg_left hpow (show 0≤X by linarith)
  have hXZ : 1 ≤ X*(Z:ℝ) := by nlinarith
  nlinarith

theorem quadraticLift_lower_count_le {X Z k : ℕ} (hX : 1 ≤ X) (hZ : 1 ≤ Z)
    (hXZ : (X : ℝ) ≤ (Z : ℝ)^(k-10)) :
    ((2*quadraticLiftHeight X Z / Z^(k-10)+1 : ℕ) : ℝ) ≤ 5*(Z:ℝ) := by
  have hZr : (0 : ℝ) < Z := by exact_mod_cast (show 0<Z by omega)
  have hH := quadraticLiftHeight_le (X:ℝ) Z (by exact_mod_cast hX) hZ
  have hHp : (quadraticLiftHeight X Z : ℝ) ≤ 2*(Z:ℝ)^(k-10)*Z := by
    nlinarith [mul_le_mul_of_nonneg_right hXZ hZr.le]
  have hdiv : (2*(quadraticLiftHeight X Z : ℝ))/(Z:ℝ)^(k-10) ≤ 4*(Z:ℝ) := by
    apply (div_le_iff₀ (pow_pos hZr _)).mpr
    nlinarith
  have hc : ((2*quadraticLiftHeight X Z / Z^(k-10) : ℕ) : ℝ) ≤
      2*(quadraticLiftHeight X Z : ℝ)/(Z:ℝ)^(k-10) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using
      (Nat.cast_div_le (m:=2*quadraticLiftHeight X Z) (n:=Z^(k-10)) :
        ((2*quadraticLiftHeight X Z / Z^(k-10) : ℕ) : ℝ) ≤
          (2*quadraticLiftHeight X Z:ℕ)/(Z^(k-10):ℕ))
  push_cast
  have hZ1 : (1:ℝ)≤Z := by exact_mod_cast hZ
  linarith

theorem quadraticLiftHeight_spacing {X Z k : ℕ} (hX : 1 ≤ X) (hZ : 2 ≤ Z)
    (hk : 10 ≤ k) (hXZ : (X : ℝ) ≤ (Z : ℝ)^(k-10)) :
    2*quadraticLiftHeight X Z < Z^(k+1) := by
  have hZr : (2:ℝ)≤Z := by exact_mod_cast hZ
  have hZpos : (0:ℝ)<Z := by linarith
  have hH := quadraticLiftHeight_le (X:ℝ) Z (by exact_mod_cast hX) (by omega)
  have hHp : 2*(quadraticLiftHeight X Z : ℝ) ≤ 4*(Z:ℝ)^(k-10)*Z := by
    nlinarith [mul_le_mul_of_nonneg_right hXZ hZpos.le]
  have hten : (4:ℝ)<(Z:ℝ)^10 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hZr 10
    norm_num at hh
    linarith
  have hid : ((Z:ℝ)^(k-10)*Z)*(Z:ℝ)^10 = (Z:ℝ)^(k+1) := by
    rw [←pow_succ,←pow_add]
    congr 1
    omega
  have hh : 2*(quadraticLiftHeight X Z : ℝ)<(Z:ℝ)^(k+1) := by
    calc
      _ ≤ 4*(Z:ℝ)^(k-10)*Z := hHp
      _ = ((Z:ℝ)^(k-10)*Z)*4 := by ring
      _ < ((Z:ℝ)^(k-10)*Z)*(Z:ℝ)^10 := mul_lt_mul_of_pos_left hten (by positivity)
      _ = _ := hid
  exact_mod_cast hh

end Ostmann.QuadraticCenter

end

end OAI
