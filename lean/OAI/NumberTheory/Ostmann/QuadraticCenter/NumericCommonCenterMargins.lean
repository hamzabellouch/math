import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericCommonCenterHeight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter

structure CommonCenterElementaryBounds (X Z J k : ℕ) : Prop where
  X_one_le : 1 ≤ X
  Z_two_le : 2 ≤ Z
  k_ten_le : 10 ≤ k
  k_le : (k : ℝ) ≤ (Z : ℝ)^(1/10:ℝ)
  J_lower : (Z : ℝ)^(9/10:ℝ) ≤ J
  J_upper : J ≤ 2*Z
  X_upper : (X : ℝ) ≤ (Z : ℝ)^(k-10)
  large : 100 ≤ (Z : ℝ)^(1/1000:ℝ)

namespace CommonCenterElementaryBounds
variable {X Z J k : ℕ} (h : CommonCenterElementaryBounds X Z J k)
include h

theorem Z_pos : (0:ℝ)<Z := by exact_mod_cast (show 0<Z by have := h.Z_two_le; omega)

theorem rpow_large {a : ℝ} (ha : 1/1000≤a) : 100 ≤ (Z:ℝ)^a :=
  h.large.trans (Real.rpow_le_rpow_of_exponent_le (by
    exact_mod_cast (show 1≤Z by have := h.Z_two_le; omega)) ha)

theorem J_one_le : (1:ℝ)≤J := by
  have hh := h.rpow_large (a:=9/10) (by norm_num)
  linarith [h.J_lower]

theorem descFactorial_half : (J:ℝ)^k/2 ≤ (J.descFactorial k:ℝ) := by
  apply descFactorial_half_pow_le (by have := h.k_ten_le; omega)
  have hk2 := pow_le_pow_left₀ (Nat.cast_nonneg k) h.k_le 2
  have hid : ((Z:ℝ)^(1/10:ℝ))^2 = (Z:ℝ)^(1/5:ℝ) := by
    rw [←Real.rpow_mul_natCast h.Z_pos.le]
    norm_num
  rw [hid] at hk2
  have hlarge : (2:ℝ)≤(Z:ℝ)^(7/10:ℝ) := by
    have := h.rpow_large (a:=7/10) (by norm_num)
    linarith
  have hh := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg h.Z_pos.le (1/5:ℝ))
  rw [←Real.rpow_add h.Z_pos] at hh
  norm_num at hh
  nlinarith [h.J_lower]

theorem cutoff_bounds : (Z:ℝ)^(3/5:ℝ)/2 ≤ (commonCenterCutoff Z:ℝ) ∧
    (commonCenterCutoff Z:ℝ) ≤ (Z:ℝ)^(3/5:ℝ) := by
  have hl := Nat.lt_floor_add_one ((Z:ℝ)^(3/5:ℝ))
  have hu := Nat.floor_le (Real.rpow_nonneg h.Z_pos.le (3/5:ℝ))
  have hlarge := h.rpow_large (a:=3/5) (by norm_num)
  change (Z:ℝ)^(3/5:ℝ)<(commonCenterCutoff Z:ℝ)+1 at hl
  exact ⟨by linarith,hu⟩

theorem cutoff_power_ten : (commonCenterCutoff Z:ℝ)^10 ≤ (Z:ℝ)^6 := by
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (commonCenterCutoff Z)) h.cutoff_bounds.2 10
  have hid : ((Z:ℝ)^(3/5:ℝ))^10 = (Z:ℝ)^6 := by
    rw [←Real.rpow_mul_natCast h.Z_pos.le]
    norm_num
  exact hh.trans_eq hid

theorem incidence_gap : 2*k*J ≤ commonCenterCutoff Z^2 := by
  have hJr : (J:ℝ)≤2*(Z:ℝ) := by exact_mod_cast h.J_upper
  have hmul := mul_le_mul h.k_le hJr (Nat.cast_nonneg J)
    (Real.rpow_nonneg h.Z_pos.le (1/10:ℝ))
  have hlarge : (16:ℝ)≤(Z:ℝ)^(1/10:ℝ) := by
    have := h.rpow_large (a:=1/10) (by norm_num)
    linarith
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(Z:ℝ)^(3/5:ℝ)/2)
    h.cutoff_bounds.1 2
  have he1 : (Z:ℝ)^(1/10:ℝ)*(Z:ℝ) = (Z:ℝ)^(11/10:ℝ) := by
    calc
      _ = (Z:ℝ)^(1/10:ℝ)*(Z:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
      _ = (Z:ℝ)^((1/10:ℝ)+1) := (Real.rpow_add h.Z_pos _ _).symm
      _ = _ := by norm_num
  have he2 : ((Z:ℝ)^(3/5:ℝ))^2 = (Z:ℝ)^(6/5:ℝ) := by
    rw [←Real.rpow_mul_natCast h.Z_pos.le]
    norm_num
  have hm := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg h.Z_pos.le (11/10:ℝ))
  rw [←Real.rpow_add h.Z_pos] at hm
  norm_num at hm
  have hinc : (2:ℝ)*k*J ≤ (commonCenterCutoff Z:ℝ)^2 := by
    rw [div_pow,he2] at hs
    have hmul' : (k:ℝ)*J≤2*(Z:ℝ)^(11/10:ℝ) := by nlinarith [he1]
    nlinarith
  exact_mod_cast hinc

theorem height_spacing : 2*quadraticLiftHeight X Z < Z^(k+1) :=
  quadraticLiftHeight_spacing h.X_one_le h.Z_two_le h.k_ten_le h.X_upper

theorem momentScale_large : 4 ≤ commonCenterMomentScale J Z k := by
  have hJpow : (J:ℝ)≤(J:ℝ)^k := le_self_pow₀ h.J_one_le (by have := h.k_ten_le; omega)
  have hbound := mul_le_mul_of_nonneg_right (h.J_lower.trans hJpow)
    (Real.rpow_nonneg h.Z_pos.le (-(7/50:ℝ)))
  rw [←Real.rpow_add h.Z_pos] at hbound
  norm_num at hbound
  have hlarge := h.rpow_large (a:=19/25) (by norm_num)
  exact (by linarith : (4:ℝ)≤(Z:ℝ)^(19/25:ℝ)).trans hbound

theorem lower_moment_negligible :
    (commonCenterCutoff Z:ℝ)^10 *
      ((J^(k-10)*(2*quadraticLiftHeight X Z/Z^(k-10)+1):ℕ):ℝ) ≤
        commonCenterMomentScale J Z k/4 := by
  have hc := quadraticLift_lower_count_le h.X_one_le (by have := h.Z_two_le; omega) h.X_upper
  have hJ10 := pow_le_pow_left₀ (Real.rpow_nonneg h.Z_pos.le (9/10:ℝ)) h.J_lower 10
  have hid10 : ((Z:ℝ)^(9/10:ℝ))^10 = (Z:ℝ)^9 := by
    rw [←Real.rpow_mul_natCast h.Z_pos.le]
    norm_num
  rw [hid10] at hJ10
  have he : (Z:ℝ)^(93/50:ℝ)*(Z:ℝ)^7 = (Z:ℝ)^9*(Z:ℝ)^(-(7/50:ℝ)) := by
    rw [←Real.rpow_natCast (Z:ℝ) 7,←Real.rpow_natCast (Z:ℝ) 9,
      ←Real.rpow_add h.Z_pos,←Real.rpow_add h.Z_pos]
    norm_num
  have hlarge : (20:ℝ)≤(Z:ℝ)^(93/50:ℝ) := by
    have := h.rpow_large (a:=93/50) (by norm_num)
    linarith
  have hmain : 20*(Z:ℝ)^7 ≤ (J:ℝ)^10*(Z:ℝ)^(-(7/50:ℝ)) := by
    calc
      _ ≤ (Z:ℝ)^(93/50:ℝ)*(Z:ℝ)^7 := mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = _ := he
      _ ≤ _ := mul_le_mul_of_nonneg_right hJ10 (Real.rpow_nonneg h.Z_pos.le _)
  have hbound : (commonCenterCutoff Z:ℝ)^10 *
      ((J^(k-10)*(2*quadraticLiftHeight X Z/Z^(k-10)+1):ℕ):ℝ) ≤
        5*(Z:ℝ)^7*(J:ℝ)^(k-10) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    calc
      _ ≤ (Z:ℝ)^6*((J:ℝ)^(k-10)*(5*(Z:ℝ))) :=
        mul_le_mul h.cutoff_power_ten
          (mul_le_mul_of_nonneg_left hc (by positivity)) (by positivity) (by positivity)
      _ = _ := by ring
  have hjpow : (J:ℝ)^10*(J:ℝ)^(k-10) = (J:ℝ)^k := by
    rw [←pow_add,Nat.add_sub_of_le h.k_ten_le]
  have hh := mul_le_mul_of_nonneg_right hmain (pow_nonneg (Nat.cast_nonneg J) (k-10))
  have hfinal : 5*(Z:ℝ)^7*(J:ℝ)^(k-10) ≤ commonCenterMomentScale J Z k/4 := by
    unfold commonCenterMomentScale
    rw [mul_right_comm ((J:ℝ)^10),hjpow] at hh
    nlinarith
  exact hbound.trans hfinal

end CommonCenterElementaryBounds
end Ostmann.QuadraticCenter

end

end OAI
