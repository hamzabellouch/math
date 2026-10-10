import OAI.MeasureTheory.Falconer.Angular.SignedStationaryRadial

namespace OAI

namespace PlanarFalconer

 theorem stationary_pair_gain_le {R l d₁ d₂ : ℝ} (hR : 0 < R) (hl : 0 < l)
    (h1 : l ≤ d₁) (h2 : l ≤ d₂) :
    (R*d₁)^(-1/2:ℝ)*(R*d₂)^(-1/2:ℝ) ≤ (R*l)⁻¹ := by
  have hb₁ := Real.rpow_le_rpow_of_nonpos (mul_pos hR hl)
    (mul_le_mul_of_nonneg_left h1 hR.le) (by norm_num : (-1/2:ℝ) ≤ 0)
  have hb₂ := Real.rpow_le_rpow_of_nonpos (mul_pos hR hl)
    (mul_le_mul_of_nonneg_left h2 hR.le) (by norm_num : (-1/2:ℝ) ≤ 0)
  calc
    _ ≤ (R*l)^(-1/2:ℝ)*(R*l)^(-1/2:ℝ) :=
      mul_le_mul hb₁ hb₂ (Real.rpow_nonneg (mul_nonneg hR.le (hl.le.trans h2)) _) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (mul_pos hR hl),show (-1/2:ℝ)+(-1/2) = -1 by norm_num,Real.rpow_neg_one]

 theorem stationary_pair_dyadic_gain {v b d₁ d₂ : ℝ}
    (h1 : (2:ℝ)^(-b) ≤ d₁) (h2 : (2:ℝ)^(-b) ≤ d₂) :
    ((2:ℝ)^v*d₁)^(-1/2:ℝ)*((2:ℝ)^v*d₂)^(-1/2:ℝ) ≤ (2:ℝ)^(-(v-b)) := by
  apply (stationary_pair_gain_le (by positivity : (0:ℝ) < (2:ℝ)^v)
    (by positivity : (0:ℝ) < (2:ℝ)^(-b)) h1 h2).trans_eq
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  congr 1

end PlanarFalconer

end OAI
