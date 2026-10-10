import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericCommonCenterParameters

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter

theorem quadraticLiftHeight_le_power (X : ℝ) (Z : ℕ) (hX : 1≤X) (hZ : 1≤Z) :
    (quadraticLiftHeight X Z:ℝ)≤2*X*(Z:ℝ)^(13/100:ℝ) := by
  have hZr : (1:ℝ)≤Z := by exact_mod_cast hZ
  have hp : 1≤(Z:ℝ)^(13/100:ℝ) := Real.one_le_rpow hZr (by norm_num)
  have hc := Nat.ceil_lt_add_one (show 0≤X*(Z:ℝ)^(13/100:ℝ) by positivity)
  change (quadraticLiftHeight X Z:ℝ)<X*(Z:ℝ)^(13/100:ℝ)+1 at hc
  nlinarith

theorem affine_numerator_range_scale {X Z m : ℕ} {h : ℤ}
    (hX : 1≤X) (hZ : 1≤Z) (hm : m≤quadraticLiftMultiplierBound Z)
    (hh : h.natAbs≤quadraticLiftHeight X Z) :
    (m*X+h.natAbs:ℕ)≤4*(X:ℝ)*(Z:ℝ)^(13/100:ℝ) := by
  have hm' : (m:ℝ)≤2*(Z:ℝ)^(13/100:ℝ) :=
    (by exact_mod_cast hm : (m:ℝ)≤quadraticLiftMultiplierBound Z).trans
      (quadraticLiftMultiplierBound_le Z hZ)
  have hh' : (h.natAbs:ℝ)≤2*(X:ℝ)*(Z:ℝ)^(13/100:ℝ) :=
    (by exact_mod_cast hh : (h.natAbs:ℝ)≤quadraticLiftHeight X Z).trans
      (quadraticLiftHeight_le_power X Z (by exact_mod_cast hX) hZ)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hm' (Nat.cast_nonneg (α := ℝ) X)]

theorem affine_numerator_range_lt_power {X Z m : ℕ} {h : ℤ}
    (hX : 1≤X) (hZ : 2≤Z) (hm : m≤quadraticLiftMultiplierBound Z)
    (hh : h.natAbs≤quadraticLiftHeight X Z) :
    m*X+h.natAbs<Z^(evenMomentParameter X Z) := by
  let k := evenMomentParameter X Z
  obtain ⟨hk,hXZ⟩ := moment_order_X_power_bound hX hZ
  have hZr : (2:ℝ)≤Z := by exact_mod_cast hZ
  have hZp : (0:ℝ)<Z := by linarith
  have hcoarse : (m*X+h.natAbs:ℕ)≤4*(X:ℝ)*Z := by
    apply (affine_numerator_range_scale hX (by omega) hm hh).trans
    have hp := Real.rpow_le_self_of_one_le (show (1:ℝ)≤Z by linarith)
      (by norm_num : (13/100:ℝ)≤1)
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hfour : (4:ℝ)<(Z:ℝ)^9 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hZr 9
    norm_num at h
    linarith
  have hid : ((Z:ℝ)^(k-10)*Z)*(Z:ℝ)^9=(Z:ℝ)^k := by
    rw [←pow_succ,←pow_add]
    congr 1
    dsimp [k]
    omega
  have hr : (m*X+h.natAbs:ℕ)<(Z:ℝ)^k := by
    calc
      _ ≤ 4*(X:ℝ)*Z := hcoarse
      _ ≤ 4*(Z:ℝ)^(k-10)*Z := by gcongr
      _ = ((Z:ℝ)^(k-10)*Z)*4 := by ring
      _ < ((Z:ℝ)^(k-10)*Z)*(Z:ℝ)^9 := mul_lt_mul_of_pos_left hfour (by positivity)
      _ = _ := hid
  exact_mod_cast hr

theorem affine_numerator_range_le_coefficient_scale {X Z m : ℕ} {h : ℤ}
    (hX : 1≤X) (hZ : 2≤Z) (hm : m≤quadraticLiftMultiplierBound Z)
    (hh : h.natAbs≤quadraticLiftHeight X Z) :
    m*X+h.natAbs≤(2*Z)^(evenMomentParameter X Z) :=
  (affine_numerator_range_lt_power hX hZ hm hh).le.trans
    (Nat.pow_le_pow_left (by omega) _)

end Ostmann.QuadraticCenter

end

end OAI
