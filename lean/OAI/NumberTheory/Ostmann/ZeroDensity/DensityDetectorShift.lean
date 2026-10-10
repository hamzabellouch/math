import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorHorizontal

namespace OAI

/-! # The exact compact detector identity at an actual zero -/

namespace Ostmann

open Complex MeasureTheory Filter
open scoped Topology

 theorem densityDetector_right_integrable (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y) :
    Integrable (fun u : ℝ => densityDetectorIntegrand χ X s Y (2 + u * I)) := by
  let K := 2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)
  have hg : Integrable (fun u : ℝ => (1 + |u|) ^ (-(2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2))
  apply (hg.const_mul (K * 8)).mono'
  · exact (densityDetectorIntegrand_line_continuous χ X s Y (by linarith) 2
      (by norm_num) (by norm_num)).aestronglyMeasurable
  · filter_upwards with u
    have hn := densityDetector_numerator_bound χ X s hs hs1 Y hY 2 u (by linarith) le_rfl
    have hk := densityDetectorKernel_line_bound 2 u (by norm_num)
    rw [densityDetectorIntegrand, norm_mul]
    apply (mul_le_mul hn hk (norm_nonneg _) (by positivity)).trans_eq
    have he : (1 + |u|) * (1 + |u|) ^ (-(3 : ℝ)) = (1 + |u|) ^ (-(2 : ℝ)) := by
      rw [show -(2 : ℝ) = 1 + -(3 : ℝ) by ring,
        Real.rpow_add (by positivity : 0 < 1 + |u|), Real.rpow_one]
    calc
      _ = K * 8 * ((1 + |u|) * (1 + |u|) ^ (-(3 : ℝ))) := by dsimp [K]; ring
      _ = _ := by rw [he]

 theorem densityDetector_zero_contour_shift (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 < s.re) (hs1 : s.re ≤ 1) (hz : χ.L s = 0)
    (Y : ℝ) (hY : 1 ≤ Y) :
    (∫ u : ℝ, densityDetectorIntegrand χ X s Y (((1 / 2 - s.re : ℝ) : ℂ) + u * I)) =
      ∫ u : ℝ, densityDetectorIntegrand χ X s Y (2 + u * I) := by
  obtain ⟨ht, hd⟩ := densityDetector_horizontal_tendsto χ X s hs.le hs1 Y hY
  apply rectangle_vertical_limit _ _ _
    (densityDetector_left_integrable χ X s hs hs1 Y hY)
    (densityDetector_right_integrable χ X s hs.le hs1 Y hY) ht hd
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact densityDetector_rectangle_zero χ X s hz Y (by linarith) (1 / 2 - s.re) 2 (-T) T
    (by linarith) (by linarith) (by norm_num) (by linarith) hT

 theorem densityDetectorMean_at_zero (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 < s.re) (hs1 : s.re ≤ 1) (hz : χ.L s = 0)
    (Y : ℝ) (hY : 1 ≤ Y) :
    densityDetectorMean χ X s Y = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
      densityDetectorIntegrand χ X s Y (((1 / 2 - s.re : ℝ) : ℂ) + u * I) := by
  rw [densityDetectorMean_eq_integral χ X s (by linarith) Y (by linarith)]
  change _ * (∫ u : ℝ, densityDetectorIntegrand χ X s Y (2 + u * I)) = _
  rw [densityDetector_zero_contour_shift χ X s hs hs1 hz Y hY]

end Ostmann

end OAI
