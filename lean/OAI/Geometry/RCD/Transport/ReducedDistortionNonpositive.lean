import OAI.Geometry.RCD.Transport.ReducedDistortionRecurrence

namespace OAI

/-! # Reduced-distortion interpolation including degenerate cases -/

open Set
open scoped ENNReal
namespace RegularPointCoordinates

theorem sigma_nonpos_interpolation {K N θ a b t : ℝ}
    (hK : K ≤ 0) (hN : 1 < N) (hθ : 0 ≤ θ)
    (ha : 0 ≤ a) (hab : a < b) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    sigma K N ((1-t)*a+t*b) θ =
      sigma K N (1-t) ((b-a)*θ)*sigma K N a θ+
      sigma K N t ((b-a)*θ)*sigma K N b θ := by
  by_cases hθ0 : θ=0
  · simp only [hθ0,mul_zero,sigma,true_or,ite_true]
    rw [←ENNReal.ofReal_mul (sub_nonneg.mpr ht1),←ENNReal.ofReal_mul ht,
      ←ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr ht1) ha)
        (mul_nonneg ht (ha.trans hab.le))]
  by_cases hK0 : K=0
  · simp only [hK0,sigma,or_true,ite_true]
    rw [←ENNReal.ofReal_mul (sub_nonneg.mpr ht1),←ENNReal.ofReal_mul ht,
      ←ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr ht1) ha)
        (mul_nonneg ht (ha.trans hab.le))]
  exact sigma_neg_interpolation (lt_of_le_of_ne hK hK0) hN
    (lt_of_le_of_ne hθ (Ne.symm hθ0)) ha hab ht ht1

theorem sigma_nonpos_zero {K N θ : ℝ} (hK : K ≤ 0) (hN : 1 < N) (hθ : 0 ≤ θ) :
    sigma K N 0 θ=0 := by
  by_cases hθ0 : θ=0
  · simp [sigma,hθ0]
  by_cases hK0 : K=0
  · simp [sigma,hK0]
  rw [sigma_neg_eq (lt_of_le_of_ne hK hK0) hN (lt_of_le_of_ne hθ (Ne.symm hθ0))]
  simp

theorem sigma_nonpos_one {K N θ : ℝ} (hK : K ≤ 0) (hN : 1 < N) (hθ : 0 ≤ θ) :
    sigma K N 1 θ=1 := by
  by_cases hθ0 : θ=0
  · simp [sigma,hθ0]
  by_cases hK0 : K=0
  · simp [sigma,hK0]
  have hp : 0<θ*Real.sqrt (-K/(N-1)) := mul_pos
    (lt_of_le_of_ne hθ (Ne.symm hθ0))
    (Real.sqrt_pos.mpr (div_pos (neg_pos.mpr (lt_of_le_of_ne hK hK0)) (sub_pos.mpr hN)))
  rw [sigma_neg_eq (lt_of_le_of_ne hK hK0) hN (lt_of_le_of_ne hθ (Ne.symm hθ0))]
  simp [div_self (Real.sinh_pos_iff.mpr hp).ne']

end RegularPointCoordinates

end OAI
