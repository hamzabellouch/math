import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySquareContour

namespace OAI

/-! # The actual Gaussian functional equation for the completed square -/

namespace Ostmann

open Complex Filter MeasureTheory
open scoped Topology Interval

 theorem densitySquareContour_limit (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    I * (∫ u : ℝ, densitySquareContour χ s (1 + u * I)) -
      I * (∫ u : ℝ, densitySquareContour χ s (-1 + u * I)) =
      (2 * (Real.pi : ℂ) * I) * densityCompletedSquare χ s := by
  obtain ⟨htop, hbot⟩ := densitySquareContour_horizontal_tendsto χ s hs
  have hr := intervalIntegral_tendsto_integral
    (densitySquareContour_vertical_integrable χ s hs 1 (by norm_num))
    tendsto_neg_atTop_atBot tendsto_id
  have hl := intervalIntegral_tendsto_integral
    (densitySquareContour_vertical_integrable χ s hs (-1) (by norm_num))
    tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hbot.sub htop).add (hr.const_mul I)).sub (hl.const_mul I)
  have hlim' : Tendsto (fun T : ℝ =>
      rectangleBoundaryIntegral (densitySquareContour χ s) (-1) 1 (-T) T) atTop
      (𝓝 (I * (∫ u : ℝ, densitySquareContour χ s (1 + u * I)) -
        I * (∫ u : ℝ, densitySquareContour χ s (-1 + u * I)))) := by
    simpa [rectangleBoundaryIntegral] using hlim
  apply tendsto_nhds_unique hlim'
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  exact (densitySquareGaussian_rectangle χ s (-1) 1 T (by norm_num) (by norm_num)
    (by linarith)).symm

 theorem densitySquareContour_left_reflection (χ : PrimitiveComplexCharacter) (s : ℂ) :
    (∫ u : ℝ, densitySquareContour χ s (-1 + u * I)) =
      -(@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        ∫ u : ℝ, densitySquareContour χ.inverse (1 - s) (1 + u * I) := by
  have he (u : ℝ) : densitySquareContour χ s (-1 + (-u) * I) =
      -(@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        densitySquareContour χ.inverse (1 - s) (1 + u * I) := by
    have hw : (-1 : ℂ) + (-u) * I = -(1 + (u : ℂ) * I) := by ring
    rw [densitySquareContour, hw, densitySquareGaussian_reflection, densitySquareContour, div_neg]
    ring
  calc
    _ = ∫ u : ℝ, densitySquareContour χ s (-1 + (-u) * I) := by
      symm
      simpa only [Complex.ofReal_neg] using
        integral_neg_eq_self (fun u : ℝ => densitySquareContour χ s (-1 + u * I)) volume
    _ = _ := by simp_rw [he]; rw [integral_const_mul]

noncomputable def densitySquareIntegral (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ u : ℝ, densitySquareContour χ s (1 + u * I)

 theorem densityCompletedSquare_equation (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    densityCompletedSquare χ s = densitySquareIntegral χ s +
      (@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        densitySquareIntegral χ.inverse (1 - s) := by
  have h := densitySquareContour_limit χ s hs
  rw [densitySquareContour_left_reflection] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : (2 * (Real.pi : ℂ)) * densityCompletedSquare χ s =
      (∫ u : ℝ, densitySquareContour χ s (1 + u * I)) +
      (@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        ∫ u : ℝ, densitySquareContour χ.inverse (1 - s) (1 + u * I) := by
    apply mul_left_cancel₀ (show (I : ℂ) ≠ 0 from I_ne_zero)
    calc
      _ = (2 * (Real.pi : ℂ) * I) * densityCompletedSquare χ s := by ring
      _ = _ := h.symm.trans (by ring)
  unfold densitySquareIntegral
  field_simp
  simp_rw [mul_comm I]
  linear_combination he

end Ostmann

end OAI
