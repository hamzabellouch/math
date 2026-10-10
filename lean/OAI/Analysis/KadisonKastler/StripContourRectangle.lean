import OAI.Analysis.KadisonKastler.StripSineQuotient

namespace OAI

/-! # The finite modular strip contour identity -/

namespace KadisonKastler

open Set

noncomputable section

theorem stripSineQuotient_rectangle (φ : ℝ) (f : ℂ → ℂ)
    (hc : ContinuousOn f {z : ℂ | |z.re| ≤ 1 / 2})
    (hd : DifferentiableOn ℂ f {z : ℂ | |z.re| < 1 / 2})
    (T : ℝ) :
    (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      stripSineQuotient φ f ((x : ℂ) + (-T : ℝ) * Complex.I)) -
    (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      stripSineQuotient φ f ((x : ℂ) + T * Complex.I)) +
    Complex.I * (∫ t : ℝ in -T..T,
      stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) -
    Complex.I * (∫ t : ℝ in -T..T,
      stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I)) = 0 := by
  have h0 : {z : ℂ | |z.re| < 1 / 2} ∈ nhds (0 : ℂ) := by
    apply (isOpen_lt Complex.continuous_re.abs continuous_const).mem_nhds
    norm_num
  have hc' := stripSineQuotient_continuousOn φ f hc (hd.differentiableAt h0)
  have hd' := stripSineQuotient_differentiableOn φ f hd
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (stripSineQuotient φ f) ((-1 / 2 : ℂ) + (-T : ℝ) * Complex.I)
    ((1 / 2 : ℂ) + T * Complex.I) ?_ ?_
  · simpa using h
  · apply hc'.mono
    intro z hz
    change z.re ∈ Set.uIcc _ _ ∧ z.im ∈ Set.uIcc _ _ at hz
    have hz' := hz.1
    norm_num at hz'
    exact abs_le.mpr hz'

  · apply hd'.mono
    intro z hz
    change z.re ∈ Ioo _ _ ∧ z.im ∈ Ioo _ _ at hz
    have hz' := hz.1
    norm_num at hz'
    exact abs_lt.mpr hz'

end

end KadisonKastler

end OAI
