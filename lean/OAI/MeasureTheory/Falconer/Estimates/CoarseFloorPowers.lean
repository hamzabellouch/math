import OAI.MeasureTheory.Falconer.Radial.PlateScales

namespace OAI

/-! # The last coarse scale interpolates to a fixed positive directional exponent -/

namespace Falconer

theorem plateScale_floor_mul (N : ℕ) (ω : ℝ) :
    plateScale ⌊ω*(N:ℝ)⌋₊ ≤ 2*(plateScale N)^ω := by
  have hf := Nat.lt_floor_add_one (ω*(N:ℝ))
  have he : -(⌊ω*(N:ℝ)⌋₊:ℝ) ≤ 1+(-(N:ℝ))*ω := by linarith only [hf]
  calc
    _ ≤ (2:ℝ)^(1+(-(N:ℝ))*ω) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = _ := by
      rw [Real.rpow_add (by norm_num),Real.rpow_one,
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rfl

theorem coarse_floor_radius_power (N : ℕ) {ω b r : ℝ}
    (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hb : 0 ≤ b)
    (hr : plateScale N ≤ r) (hr1 : r ≤ 1) (D : ℝ) :
    (max (D*r) (plateScale ⌊ω*(N:ℝ)⌋₊))^b ≤
      (2*max D 1)^b*r^(ω*b) := by
  have hr0 : 0 < r := (plateScale_pos N).trans_le hr
  have hrpow : r ≤ r^ω := by
    calc
      r = r^(1:ℝ) := (Real.rpow_one r).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hω1
  have hmax : 1 ≤ max D 1 := le_max_right _ _
  have hD : 0 ≤ max D 1 := zero_le_one.trans hmax
  have hscale : plateScale ⌊ω*(N:ℝ)⌋₊ ≤ (2*max D 1)*r^ω := by
    calc
      _ ≤ 2*(plateScale N)^ω := plateScale_floor_mul N ω
      _ ≤ 2*r^ω := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (plateScale_pos N).le hr hω) (by norm_num)
      _ ≤ _ := by nlinarith only [hmax,Real.rpow_nonneg hr0.le ω]
  have hDr : D*r ≤ (2*max D 1)*r^ω := by
    have h₁ := mul_le_mul (le_max_left D 1) hrpow hr0.le hD
    have h₂ : 0 ≤ max D 1*r^ω := mul_nonneg hD (Real.rpow_nonneg hr0.le _)
    nlinarith only [h₁,h₂]
  apply (Real.rpow_le_rpow
    ((plateScale_pos _).le.trans (le_max_right _ _)) (max_le hDr hscale) hb).trans_eq
  rw [Real.mul_rpow (mul_nonneg (by norm_num) hD) (Real.rpow_nonneg hr0.le _),
    ← Real.rpow_mul hr0.le]

end Falconer

end OAI
