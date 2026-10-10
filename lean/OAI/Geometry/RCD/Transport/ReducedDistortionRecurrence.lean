import OAI.Geometry.RCD.Transport.RenyiMidpointCompression
import OAI.Geometry.RCD.Transport.HyperbolicDistortion

namespace OAI

/-! # Exact interpolation of reduced distortion coefficients

The identities underlying Rajala, arXiv:1202.6514, Lemma 3.2. The
coefficient `sigma K N` has denominator `N-1`; the reduced CD(K,N)
coefficient is therefore `sigma K (N+1)`.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem sinh_interpolation_product (a d u : ℝ) :
    Real.sinh (a+u)*Real.sinh d =
      Real.sinh (d-u)*Real.sinh a+Real.sinh u*Real.sinh (a+d) := by
  rw [Real.sinh_add,Real.sinh_sub,Real.sinh_add]
  ring

theorem sin_interpolation_product (a d u : ℝ) :
    Real.sin (a+u)*Real.sin d =
      Real.sin (d-u)*Real.sin a+Real.sin u*Real.sin (a+d) := by
  rw [Real.sin_add,Real.sin_sub,Real.sin_add]
  ring

theorem sinh_ratio_interpolation (z a b t : ℝ)
    (hz : Real.sinh z ≠ 0) (hd : Real.sinh ((b-a)*z) ≠ 0) :
    Real.sinh (((1-t)*a+t*b)*z)/Real.sinh z =
      Real.sinh ((1-t)*((b-a)*z))/Real.sinh ((b-a)*z)*(Real.sinh (a*z)/Real.sinh z)+
      Real.sinh (t*((b-a)*z))/Real.sinh ((b-a)*z)*(Real.sinh (b*z)/Real.sinh z) := by
  have h := sinh_interpolation_product (a*z) ((b-a)*z) (t*((b-a)*z))
  rw [show a*z+t*((b-a)*z)=((1-t)*a+t*b)*z by ring,
    show (b-a)*z-t*((b-a)*z)=(1-t)*((b-a)*z) by ring,
    show a*z+(b-a)*z=b*z by ring] at h
  simp only [mul_comm, mul_left_comm, mul_assoc] at h hz hd ⊢
  field_simp
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

theorem sin_ratio_interpolation (z a b t : ℝ)
    (hz : Real.sin z ≠ 0) (hd : Real.sin ((b-a)*z) ≠ 0) :
    Real.sin (((1-t)*a+t*b)*z)/Real.sin z =
      Real.sin ((1-t)*((b-a)*z))/Real.sin ((b-a)*z)*(Real.sin (a*z)/Real.sin z)+
      Real.sin (t*((b-a)*z))/Real.sin ((b-a)*z)*(Real.sin (b*z)/Real.sin z) := by
  have h := sin_interpolation_product (a*z) ((b-a)*z) (t*((b-a)*z))
  rw [show a*z+t*((b-a)*z)=((1-t)*a+t*b)*z by ring,
    show (b-a)*z-t*((b-a)*z)=(1-t)*((b-a)*z) by ring,
    show a*z+(b-a)*z=b*z by ring] at h
  simp only [mul_comm, mul_left_comm, mul_assoc] at h hz hd ⊢
  field_simp
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

theorem sigma_neg_interpolation {K N θ a b t : ℝ}
    (hK : K < 0) (hN : 1 < N) (hθ : 0 < θ)
    (ha : 0 ≤ a) (hab : a < b) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    sigma K N ((1-t)*a+t*b) θ =
      sigma K N (1-t) ((b-a)*θ)*sigma K N a θ+
      sigma K N t ((b-a)*θ)*sigma K N b θ := by
  let z := θ*Real.sqrt (-K/(N-1))
  have hz : 0 < z := mul_pos hθ (Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hK) (sub_pos.mpr hN)))
  have hd : 0 < (b-a)*z := mul_pos (sub_pos.mpr hab) hz
  have hθd : 0 < (b-a)*θ := mul_pos (sub_pos.mpr hab) hθ
  simp only [sigma_neg_eq hK hN hθ, sigma_neg_eq hK hN hθd, mul_assoc]
  change ENNReal.ofReal (Real.sinh (((1-t)*a+t*b)*z)/Real.sinh z) =
    ENNReal.ofReal (Real.sinh ((1-t)*((b-a)*z))/Real.sinh ((b-a)*z))*
      ENNReal.ofReal (Real.sinh (a*z)/Real.sinh z)+
    ENNReal.ofReal (Real.sinh (t*((b-a)*z))/Real.sinh ((b-a)*z))*
      ENNReal.ofReal (Real.sinh (b*z)/Real.sinh z)
  have h0 : 0 ≤ Real.sinh ((1-t)*((b-a)*z))/Real.sinh ((b-a)*z) :=
    div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg (sub_nonneg.mpr ht1) hd.le))
      (Real.sinh_nonneg_iff.mpr hd.le)
  have h1 : 0 ≤ Real.sinh (t*((b-a)*z))/Real.sinh ((b-a)*z) :=
    div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg ht hd.le)) (Real.sinh_nonneg_iff.mpr hd.le)
  have hA : 0 ≤ Real.sinh (a*z)/Real.sinh z :=
    div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg ha hz.le)) (Real.sinh_nonneg_iff.mpr hz.le)
  have hB : 0 ≤ Real.sinh (b*z)/Real.sinh z :=
    div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg (ha.trans hab.le) hz.le))
      (Real.sinh_nonneg_iff.mpr hz.le)
  rw [←ENNReal.ofReal_mul h0,←ENNReal.ofReal_mul h1,←ENNReal.ofReal_add
    (mul_nonneg h0 hA) (mul_nonneg h1 hB)]
  congr 1
  exact sinh_ratio_interpolation z a b t (Real.sinh_pos_iff.mpr hz).ne'
    (Real.sinh_pos_iff.mpr hd).ne'

end RegularPointCoordinates

end

end OAI
