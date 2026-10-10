import OAI.Geometry.RCD.Transport.ScaledRadialTransport

namespace OAI

/-! # Constants uniform in the shrinking transport radius -/

open Metric

noncomputable section
namespace RegularPointCoordinates

theorem scaled_transport_constants {n : ℕ} {R : ℝ} (hR : 0 < R) :
    let β := transportCutoffExponent n
    let D := (R ^ (-β) - (3 * R) ^ (-β)) / β
    let Q := R ^ (-(β + 1))
    let m := (R / 2) * (2 * R) ^ (-(β + 1))
    let q := (2 : ℝ) ^ (β + 2)
    0 < m ∧ 0 ≤ D ∧ D / m ≤ q / β ∧ Q / (R * m) * R ^ 2 = q := by
  dsimp only
  let β := transportCutoffExponent n
  let m := (R / 2) * (2 * R) ^ (-(β + 1))
  let q := (2 : ℝ) ^ (β + 2)
  have hβ : 0 < β := transportCutoffExponent_pos n
  have hm : 0 < m := by dsimp only [m]; positivity
  have hpow : (2 : ℝ) ^ (β + 2) * (2 : ℝ) ^ (-(β + 1)) = 2 := by
    rw [← Real.rpow_add (by norm_num)]
    have he : β + 2 + -(β + 1) = 1 := by ring
    rw [he, Real.rpow_one]
  have hRpow : R * R ^ (-(β + 1)) = R ^ (-β) := by
    calc
      _ = R ^ (1 : ℝ) * R ^ (-(β + 1)) := by rw [Real.rpow_one]
      _ = R ^ (1 + -(β + 1)) := (Real.rpow_add hR _ _).symm
      _ = _ := by congr 1; ring
  have hmq : m * q = R * R ^ (-(β + 1)) := by
    dsimp only [m, q]
    rw [Real.mul_rpow (by norm_num) hR.le]
    calc
      _ = (R / 2) * R ^ (-(β + 1)) *
          ((2 : ℝ) ^ (β + 2) * (2 : ℝ) ^ (-(β + 1))) := by ring
      _ = _ := by rw [hpow]; ring
  have hD : 0 ≤ (R ^ (-β) - (3 * R) ^ (-β)) / β := by
    apply div_nonneg _ hβ.le
    exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hR (by linarith) (by linarith))
  refine ⟨hm, hD, ?_, ?_⟩
  · apply (div_le_iff₀ hm).mpr
    calc
      _ ≤ R ^ (-β) / β := div_le_div_of_nonneg_right
        (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) hβ.le
      _ = (q / β) * m := by rw [← hRpow, ← hmq]; ring
  · have heq : R ^ (-(β + 1)) * R ^ 2 = q * (R * m) := by
      rw [mul_left_comm q R m, mul_comm q m, hmq]
      ring
    calc
      R ^ (-(β + 1)) / (R * m) * R ^ 2 =
          (R ^ (-(β + 1)) * R ^ 2) / (R * m) := by ring
      _ = q := (div_eq_iff (ne_of_gt (mul_pos hR hm))).mpr heq

end RegularPointCoordinates

end

end OAI
