import Mathlib.Tactic

namespace OAI

/-! # Scalar normalization estimates for recursive interpolation -/

namespace PolycyclicRecognition

private theorem mass_fraction_left_le {A B u v : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B)
    (hv : 0 ≤ v) (hvB : v ≤ B) :
    A * |u / A - v / B| ≤ |u - v| + |A - B| := by
  have hid : A * |u / A - v / B| = |(u * B - A * v) / B| := by
    calc
      _ = |A * (u / A - v / B)| := by rw [abs_mul, abs_of_pos hA]
      _ = _ := by congr 1; field_simp
  rw [hid, abs_of_nonpos (sub_nonpos.mpr hAB)]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hB).mpr
    have ha := neg_abs_le (u - v)
    nlinarith [mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hvB),
      mul_le_mul_of_nonneg_right ha hB.le]
  · apply (div_le_iff₀ hB).mpr
    have ha := le_abs_self (u - v)
    nlinarith [mul_nonneg (sub_nonneg.mpr hAB) hv,
      mul_le_mul_of_nonneg_right ha hB.le]

/-- Normalization of a partial mass costs at most its own change plus
the change of the total mass, after multiplication by the smaller total. -/
theorem min_mass_mul_abs_fraction_sub_le {A B u v : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hu : 0 ≤ u) (huA : u ≤ A)
    (hv : 0 ≤ v) (hvB : v ≤ B) :
    min A B * |u / A - v / B| ≤ |u - v| + |A - B| := by
  rcases le_total A B with h | h
  · rw [min_eq_left h]
    exact mass_fraction_left_le hA hB h hv hvB
  · rw [min_eq_right h]
    simpa only [abs_sub_comm] using mass_fraction_left_le hB hA h hu huA

/-- The smaller normalized partial mass, rescaled by the smaller total,
never exceeds either original partial mass. -/
theorem min_mass_mul_min_fraction_le {A B u v : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    min A B * min (u / A) (v / B) ≤ min u v := by
  have hm : 0 ≤ min A B := le_min hA.le hB.le
  apply le_min
  · calc
      _ ≤ min A B * (u / A) := mul_le_mul_of_nonneg_left (min_le_left _ _) hm
      _ ≤ A * (u / A) := mul_le_mul_of_nonneg_right (min_le_left _ _) (div_nonneg hu hA.le)
      _ = u := by field_simp
  · calc
      _ ≤ min A B * (v / B) := mul_le_mul_of_nonneg_left (min_le_right _ _) hm
      _ ≤ B * (v / B) := mul_le_mul_of_nonneg_right (min_le_right _ _) (div_nonneg hv hB.le)
      _ = v := by field_simp

end PolycyclicRecognition

end OAI
