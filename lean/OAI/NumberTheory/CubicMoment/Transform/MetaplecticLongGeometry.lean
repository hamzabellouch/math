import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedPowers

namespace OAI

/-! The natural dual cutoff in the long-primal branch gives precisely
the quarter-conductor, square-root-height factor. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_long_natural_length {R T X : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hX : 0 < X)
    (hlong : Real.sqrt R*T^2 ≤ X) :
    R^2*T^4/X ≤ R*Real.sqrt R*T^2 := by
  apply (div_le_iff₀ hX).mpr
  have hs := Real.sq_sqrt hR.le
  have hh := mul_le_mul_of_nonneg_left hlong
    (show 0 ≤ R*Real.sqrt R*T^2 by positivity)
  have he : R*Real.sqrt R*T^2*(Real.sqrt R*T^2) = R^2*T^4 := by
    calc
      _ = R*(Real.sqrt R)^2*T^4 := by ring
      _ = _ := by rw [hs]; ring
  simpa only [he] using hh

lemma metaplectic_long_cutoff {Y R T X δ : ℝ}
    (hY : 1 ≤ Y) (hR : 1 ≤ R) (hT : 1 ≤ T) (hX : 0 < X)
    (hδ : 0 ≤ δ) (hlong : Real.sqrt R*T^2 ≤ X) :
    max 1 (Y^δ*(R^2*T^4/X)) ≤ 2*Y^δ*R*Real.sqrt R*T^2 := by
  have hYδ : 1 ≤ Y^δ := Real.one_le_rpow hY hδ
  have hRs : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
  have hT2 : 1 ≤ T^2 := one_le_pow₀ hT
  have hbase : 1 ≤ Y^δ*R*Real.sqrt R*T^2 := by
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hYδ hR) hRs) hT2
  have hnat := metaplectic_long_natural_length (zero_lt_one.trans_le hR)
    (zero_lt_one.trans_le hT) hX hlong
  apply max_le
  · nlinarith only [hbase]
  · calc
      _ ≤ Y^δ*(R*Real.sqrt R*T^2) :=
        mul_le_mul_of_nonneg_left hnat (Real.rpow_nonneg (zero_le_one.trans hY) _)
      _ ≤ _ := by nlinarith only [hbase]

lemma metaplectic_long_sqrt_factor {Y R T J δ : ℝ}
    (hY : 1 ≤ Y) (hR : 1 ≤ R) (hT : 1 ≤ T) (hδ : 0 ≤ δ)
    (hJ : J ≤ 2*Y^δ*R*Real.sqrt R*T^2) :
    1+Real.sqrt (4*J/(R*T)) ≤ 4*Y^(δ/2)*R^(1/4:ℝ)*Real.sqrt T := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let H := Y^(δ/2)*R^(1/4:ℝ)*Real.sqrt T
  have hH : 1 ≤ H := by
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hY (by positivity))
      (Real.one_le_rpow hR (by norm_num))) (Real.one_le_sqrt.mpr hT)
  have hHsq : H^2 = Y^δ*Real.sqrt R*T := by
    dsimp [H]
    rw [mul_pow,mul_pow,Real.sq_sqrt hTp.le,
      ←Real.rpow_mul_natCast hYp.le,←Real.rpow_mul_natCast hRp.le]
    norm_num only [Nat.cast_ofNat]
    rw [show δ/2*2 = δ by ring,←Real.sqrt_eq_rpow]
  have harg : 4*J/(R*T) ≤ 8*H^2 := by
    apply (div_le_iff₀ (mul_pos hRp hTp)).mpr
    rw [hHsq]
    nlinarith only [hJ]
  have hs : Real.sqrt (4*J/(R*T)) ≤ 3*H := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 3*H)).mpr
    nlinarith only [harg,sq_nonneg H]
  have hout : 1+Real.sqrt (4*J/(R*T)) ≤ 4*H := by linarith
  simpa only [H,mul_assoc] using hout

end CubicFirstMoment

end

end OAI
