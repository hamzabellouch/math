import OAI.Analysis.KadisonKastler.FrequencyNest

namespace OAI

/-! # Fourier transformation of the actual regular translations

The identity is first proved on Schwartz vectors and extended by their
norm density. Its normalization is explicit: translating by `s` becomes
multiplication by `exp(2*pi*i*s*ξ)`.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def translatedSchwartz (s : ℝ) (f : SchwartzMap ℝ H) : SchwartzMap ℝ H :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (by fun_prop)
    (isometry_add_right s).antilipschitzWith f

omit [CompleteSpace H] in
private theorem translatedSchwartz_toLp (s : ℝ) (f : SchwartzMap ℝ H) :
    (translatedSchwartz s f).toLp 2 = regularTranslateApply s (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(translatedSchwartz s f).coeFn_toLp 2,
    regularTranslateApply_ae s (f.toLp 2),
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae_eq_comp
      (f.coeFn_toLp 2)] with t h₁ h₂ h₃
  exact h₁.trans (h₃.symm.trans h₂.symm)

omit [CompleteSpace H] in
private theorem fourier_translate_function (s : ℝ) (f : ℝ → H) (x : ℝ) :
    𝓕 (f ∘ fun t => t + s) x = regularCharacterScalar (2 * Real.pi * s) x • 𝓕 f x := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ ℝ) f s) x
  change 𝓕 (f ∘ fun t => t + s) x = _ at h
  convert h using 1
  simp only [Circle.smul_def, innerₗ_apply_apply, Real.inner_apply,
    regularCharacterScalar, Real.fourierChar_apply', mul_assoc]
  rfl

private theorem fourier_translate_schwartz (s : ℝ) (f : SchwartzMap ℝ H) :
    (𝓕 (regularTranslateApply s (f.toLp 2)) : RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (𝓕 (f.toLp 2)) := by
  rw [← translatedSchwartz_toLp, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (translatedSchwartz s f)).coeFn_toLp 2,
    (𝓕 f).coeFn_toLp 2,
    regularCharacterUnitary_apply_ae (2 * Real.pi * s) ((𝓕 f).toLp 2)]
    with t h₁ h₂ h₃
  rw [h₁, h₃, h₂]
  exact fourier_translate_function s f t

/-- Plancherel's transform intertwines the two concrete unitary actions. -/
theorem fourier_regularTranslateApply (s : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 (regularTranslateApply s f) : RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (𝓕 f) := by
  let F : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := Lp.fourierTransformₗᵢ ℝ H
  let T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := (regularTranslationEquiv (H := H) s :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  let C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularCharacterUnitary (H := H) (2 * Real.pi * s)
  have he : F.comp T = C.comp F := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
      (p := 2) ENNReal.ofNat_ne_top).equalizer
      (F.comp T).continuous (C.comp F).continuous
    funext g
    exact fourier_translate_schwartz s g
  exact congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f) he

end

end KadisonKastler

end OAI
