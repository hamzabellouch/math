import OAI.NumberTheory.CubicMoment.Estimates.CommonNonzeroBound
import OAI.NumberTheory.CubicMoment.Estimates.CommonOuterPowers

namespace OAI

/-! Power saving for the nonzero modes of genuinely shortened rows. -/
noncomputable section
namespace CubicFirstMoment

lemma commonNonzeroCost_power_saving {C B Q A L δ η : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQL : Q ≤ L)
    (hL : 1 ≤ L) (hA : 0 < A) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hηδ : η ≤ δ) (hAL : L^(1-η) ≤ A) :
    commonNonzeroCost C (δ/100) B Q A L (L^δ) ≤
      3*C*B^(δ/100)*A^(2/3:ℝ)*L^(2/3:ℝ)*L^(-δ/4) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA1 : 1 ≤ A := (Real.one_le_rpow hL (by linarith : 0 ≤ 1-η)).trans hAL
  have hmax : max 1 (L/L^δ) = L^(1-δ) := by
    have he : L/L^δ = L^(1-δ) := by rw [Real.rpow_sub hLp,Real.rpow_one]
    rw [he]
    exact max_eq_right (Real.one_le_rpow hL (by linarith))
  unfold commonNonzeroCost
  rw [hmax]
  have hp := common_outer_scale_small_power hB hQ hQL hL hA1 hδ
  have hb := shortened_poisson_polynomial hL hA (by positivity) hδ hηδ hAL le_rfl
  calc
    _ ≤ C*(B^(δ/100)*L^(δ/20))*(3*A^(2/3:ℝ)*L^(2/3:ℝ)*L^(-δ/3)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hC) hb (by positivity) (by positivity)
    _ = (3*C*B^(δ/100)*A^(2/3:ℝ)*L^(2/3:ℝ))*L^(δ/20-δ/3) := by
      rw [Real.rpow_sub hLp,show -δ/3 = -(δ/3) by ring,Real.rpow_neg hLp.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

end CubicFirstMoment

end

end OAI
