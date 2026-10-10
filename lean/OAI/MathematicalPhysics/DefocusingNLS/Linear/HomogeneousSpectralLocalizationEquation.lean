import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationPotential

namespace OAI

/-! Exact two-channel Schrodinger equations after the radial Liouville transform. -/

namespace DefocusingNLS

noncomputable def homogeneousSpectralLocalizationFrequency
    (h b eta omega r : ℝ) : ℝ :=
  r^2 / 16 + b - h * omega - (eta + 99 / 4) / r^2

theorem homogeneousSpectralLocalization_centrifugal (ell : ℕ) :
    (ell : ℝ) * (ell + 10) + 99 / 4 = ((ell : ℝ) + 5)^2 - 1 / 4 := by ring

private theorem localization_source (A B D C f g : ℂ) (hB : B ≠ 0) :
    A * (D * f + C * g) = D * (A * f) + C * (A / B) * (B * g) := by
  field_simp [hB]

theorem homogeneousSpectralLocalization_eigenpair
    (a b eta : ℝ) (m : ℕ) (Q : ℝ → ℂ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g)
    (r : ℝ) (hr : 0 < r) :
    let P := homogeneousSpectralLocalizationState 1 (fun t => (f t, deriv f t))
    let M := homogeneousSpectralLocalizationState (-1) (fun t => (g t, deriv g t))
    let D := spectralDiagonalCoefficient m (Q r)
    let C := spectralCrossCoefficient m (Q r)
    HasDerivAt P ((P r).2,
      -((homogeneousSpectralLocalizationFrequency 1 b eta lam.im r : ℂ) +
        Complex.I * ((a + lam.re - 3 : ℝ) : ℂ)) * (P r).1 +
      D * (P r).1 + C * (homogeneousSpectralLocalizationFactor 1 r /
        homogeneousSpectralLocalizationFactor (-1) r) * (M r).1) r ∧
    HasDerivAt M ((M r).2,
      -((homogeneousSpectralLocalizationFrequency (-1) b eta lam.im r : ℂ) -
        Complex.I * ((a + lam.re - 3 : ℝ) : ℂ)) * (M r).1 +
      star D * (M r).1 + star C * (homogeneousSpectralLocalizationFactor (-1) r /
        homogeneousSpectralLocalizationFactor 1 r) * (P r).1) r := by
  intro P M D C
  have hd := harmonicRadialState_hasDerivAt a b m Q f g (eta : ℂ) lam hf hg he r hr
  have hp := (ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt r hd
  have hm := (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt r hd
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at hp hm
  have hplus : HasDerivAt (fun t => (f t, deriv f t))
      (deriv f r, -2 * homogeneousSpectralLocalizationSlope 1 r * deriv f r +
        (-(b : ℂ) - Complex.I * ((a : ℂ) + lam) + (eta : ℂ) / (r : ℂ)^2) * f r +
        (D * f r + C * g r)) r := by
    change HasDerivAt (fun t => (f t, deriv f t)) _ r at hp
    apply hp.congr_deriv
    apply Prod.ext
    · rfl
    · dsimp only [spectralPhysicalCircularField, harmonicRadialState,
        homogeneousSpectralLocalizationSlope, D, C]
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
  have hminus : HasDerivAt (fun t => (g t, deriv g t))
      (deriv g r, -2 * homogeneousSpectralLocalizationSlope (-1) r * deriv g r +
        (-(b : ℂ) + Complex.I * ((a : ℂ) + lam) + (eta : ℂ) / (r : ℂ)^2) * g r +
        (star D * g r + star C * f r)) r := by
    change HasDerivAt (fun t => (g t, deriv g t)) _ r at hm
    apply hm.congr_deriv
    apply Prod.ext
    · rfl
    · dsimp only [spectralPhysicalCircularField, harmonicRadialState,
        homogeneousSpectralLocalizationSlope, D, C]
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
  have hP := homogeneousSpectralLocalizationState_hasDerivAt 1 r hr _
    (-(b : ℂ) - Complex.I * ((a : ℂ) + lam) + (eta : ℂ) / (r : ℂ)^2)
    (D * f r + C * g r) hplus
  have hM := homogeneousSpectralLocalizationState_hasDerivAt (-1) r hr _
    (-(b : ℂ) + Complex.I * ((a : ℂ) + lam) + (eta : ℂ) / (r : ℂ)^2)
    (star D * g r + star C * f r) hminus
  have hAp : homogeneousSpectralLocalizationFactor 1 r ≠ 0 := Complex.exp_ne_zero _
  have hAm : homogeneousSpectralLocalizationFactor (-1) r ≠ 0 := Complex.exp_ne_zero _
  constructor
  · apply hP.congr_deriv
    apply Prod.ext
    · rfl
    · have hc := homogeneousSpectralLocalization_coefficient 1 r a b eta lam hr (by norm_num)
      norm_num at hc
      rw [hc]
      dsimp only [P, M, homogeneousSpectralLocalizationState, homogeneousSpectralLocalizationFrequency]
      rw [localization_source _ _ D C (f r) (g r) hAm]
      push_cast
      ring
  · apply hM.congr_deriv
    apply Prod.ext
    · rfl
    · have hc := homogeneousSpectralLocalization_coefficient (-1) r a b eta lam hr (by norm_num)
      norm_num at hc
      rw [hc]
      dsimp only [P, M, homogeneousSpectralLocalizationState, homogeneousSpectralLocalizationFrequency]
      rw [localization_source _ _ (star D) (star C) (g r) (f r) hAp]
      push_cast
      ring

end DefocusingNLS

end OAI
