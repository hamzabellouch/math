import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.GaussianTimeBlock
import OAI.Geometry.RCD.Heat.GaussianHeatInput

namespace OAI

/-! # One uniform Gaussian majorant for all cutoff kernels in a time block -/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The published Gaussian bound gives one coefficient before the scale,
pole and cutoff are chosen. Volume control is needed only on its support. -/
theorem cutoff_gaussian_block_bound (μ : Measure X) {ker : ℝ → X → X → ℝ}
    (hg : HasCoordinateHeatBounds μ ker) (n : ℕ) {V : ℝ} (hV : 0 < V) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ r t : ℝ, 0 < r → r ≤ 1 → 0 < t → t ≤ r ^ 2 →
      ∀ (p : X) (χ : X → ℝ), (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) →
      (∀ z, χ z ≠ 0 → V * r ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ q : ℝ, 0 ≤ q → ∀ z : X, q * r ≤ dist p z →
        χ z * ker t p z ≤ (C / r ^ n) * Real.exp (-q ^ 2 / D) := by
  obtain ⟨C₁, B, hC₁, hB, hgauss⟩ := hg (1 / 2) (by norm_num) (by norm_num)
  let C := C₁ * Real.exp B / V
  have hC : 0 < C := div_pos (mul_pos hC₁ (Real.exp_pos _)) hV
  refine ⟨C, 4 + 1 / 2, hC, by norm_num, ?_⟩
  intro r t hr hr1 ht htr p χ hχ hvol q hq z hsep
  by_cases hz : χ z = 0
  · rw [hz, zero_mul]
    positivity
  have hbound := gaussian_time_displacement_upper μ ker n ht htr hr hq hC₁.le hV
    (by norm_num : (0 : ℝ) < 4 + 1 / 2) hB p z (hgauss t ht p z).2 (hvol z hz) hsep
  have hker0 : 0 ≤ ker t p z := by
    apply le_trans _ (hgauss t ht p z).1
    positivity
  have hcoeff : (C₁ / (V * r ^ n)) * Real.exp (B * r ^ 2) ≤ C / r ^ n := by
    calc
      _ ≤ (C₁ / (V * r ^ n)) * Real.exp B :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          have hs : r ^ 2 ≤ 1 := by nlinarith
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hB))
          (div_nonneg hC₁.le (mul_pos hV (pow_pos hr n)).le)
      _ = _ := by dsimp only [C]; field_simp
  exact (mul_le_of_le_one_left hker0 (hχ z).2).trans
    (hbound.trans (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le))

end RegularPointCoordinates

end

end OAI
