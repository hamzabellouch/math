import OAI.Geometry.RCD.Transport.ReducedDistortionRecurrence

namespace OAI

/-! # Reduced distortion interpolation in positive curvature

The conjugate-radius restriction is explicit. No identity involving an
undefined quotient at a conjugate point is used.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem sigma_pos_eq {K N θ : ℝ} (hK : 0 < K) (hN : 1 < N) (hθ : 0 < θ)
    (hc : θ*Real.sqrt (K/(N-1)) < Real.pi) (t : ℝ) :
    sigma K N t θ = ENNReal.ofReal (Real.sin (t*(θ*Real.sqrt (K/(N-1)))) /
      Real.sin (θ*Real.sqrt (K/(N-1)))) := by
  have hNm : 0 < N-1 := sub_pos.mpr hN
  have hz : 0 < θ*Real.sqrt (K/(N-1)) := mul_pos hθ (Real.sqrt_pos.mpr (div_pos hK hNm))
  have he : (θ*Real.sqrt (K/(N-1)))^2 = K*θ^2/(N-1) := by
    rw [mul_pow,Real.sq_sqrt (div_nonneg hK.le hNm.le)]
    ring
  have hbound : ¬ (N-1)*Real.pi^2 ≤ K*θ^2 := by
    have hs : (θ*Real.sqrt (K/(N-1)))^2 < Real.pi^2 := by nlinarith
    rw [he,div_lt_iff₀ hNm] at hs
    exact not_le.mpr (by nlinarith)
  simp only [sigma,hθ.ne',hK.ne',or_self,ite_false,hbound,ite_eq_left hK,mul_assoc]

theorem sigma_pos_interpolation {K N θ a b t : ℝ}
    (hK : 0 < K) (hN : 1 < N) (hθ : 0 < θ)
    (hc : θ*Real.sqrt (K/(N-1)) < Real.pi)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    sigma K N ((1-t)*a+t*b) θ =
      sigma K N (1-t) ((b-a)*θ)*sigma K N a θ+
      sigma K N t ((b-a)*θ)*sigma K N b θ := by
  let z := θ*Real.sqrt (K/(N-1))
  have hz : 0 < z := mul_pos hθ (Real.sqrt_pos.mpr (div_pos hK (sub_pos.mpr hN)))
  have hd : 0 < (b-a)*z := mul_pos (sub_pos.mpr hab) hz
  have hdle : (b-a)*z ≤ z := by nlinarith
  have hdpi : (b-a)*z < Real.pi := hdle.trans_lt hc
  have hθd : 0 < (b-a)*θ := mul_pos (sub_pos.mpr hab) hθ
  have hdc : ((b-a)*θ)*Real.sqrt (K/(N-1)) < Real.pi := by
    simpa only [mul_assoc] using hdpi
  simp only [sigma_pos_eq hK hN hθ hc,sigma_pos_eq hK hN hθd hdc,mul_assoc]
  change ENNReal.ofReal (Real.sin (((1-t)*a+t*b)*z)/Real.sin z) =
    ENNReal.ofReal (Real.sin ((1-t)*((b-a)*z))/Real.sin ((b-a)*z))*
      ENNReal.ofReal (Real.sin (a*z)/Real.sin z)+
    ENNReal.ofReal (Real.sin (t*((b-a)*z))/Real.sin ((b-a)*z))*
      ENNReal.ofReal (Real.sin (b*z)/Real.sin z)
  have hsz : 0 < Real.sin z := Real.sin_pos_of_pos_of_lt_pi hz hc
  have hsd : 0 < Real.sin ((b-a)*z) := Real.sin_pos_of_pos_of_lt_pi hd hdpi
  have h0 : 0 ≤ Real.sin ((1-t)*((b-a)*z))/Real.sin ((b-a)*z) :=
    div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (sub_nonneg.mpr ht1) hd.le)
      (by nlinarith)) hsd.le
  have h1 : 0 ≤ Real.sin (t*((b-a)*z))/Real.sin ((b-a)*z) :=
    div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg ht hd.le) (by nlinarith)) hsd.le
  have hA : 0 ≤ Real.sin (a*z)/Real.sin z :=
    div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg ha hz.le) (by nlinarith)) hsz.le
  have hB : 0 ≤ Real.sin (b*z)/Real.sin z :=
    div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (ha.trans hab.le) hz.le)
      (by nlinarith)) hsz.le
  rw [←ENNReal.ofReal_mul h0,←ENNReal.ofReal_mul h1,←ENNReal.ofReal_add
    (mul_nonneg h0 hA) (mul_nonneg h1 hB)]
  congr 1
  exact sin_ratio_interpolation z a b t hsz.ne' hsd.ne'

end RegularPointCoordinates

end

end OAI
