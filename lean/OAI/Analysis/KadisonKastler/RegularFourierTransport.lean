import OAI.Analysis.KadisonKastler.FourierModulation

namespace OAI

/-! # Fourier transport of constant operators and real translations -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem postcomp_toLp (b : H →L[ℂ] H) (f : SchwartzMap ℝ H) :
    (SchwartzMap.postcompCLM b f).toLp 2 = regularConstantHom volume b (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(SchwartzMap.postcompCLM b f).coeFn_toLp 2, f.coeFn_toLp 2,
    regularConstantHom_apply_ae volume b (f.toLp 2)] with t h₁ h₂ h₃
  rw [h₁, h₃, h₂]
  rfl

private theorem fourier_postcomp (b : H →L[ℂ] H) (f : SchwartzMap ℝ H) (t : ℝ) :
    (𝓕 (SchwartzMap.postcompCLM b f)) t = b ((𝓕 f) t) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  simp only [Real.fourier_eq, SchwartzMap.postcompCLM_apply]
  rw [← b.integral_comp_comm ((Real.fourierIntegral_convergent_iff t).mpr f.integrable)]
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [Circle.smul_def, map_smul]

private theorem fourier_constant_schwartz (b : H →L[ℂ] H) (f : SchwartzMap ℝ H) :
    (𝓕 (regularConstantHom volume b (f.toLp 2)) : RegularCoreHilbert H) =
      regularConstantHom volume b (𝓕 (f.toLp 2)) := by
  rw [← postcomp_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (SchwartzMap.postcompCLM b f)).coeFn_toLp 2,
    (𝓕 f).coeFn_toLp 2, regularConstantHom_apply_ae volume b ((𝓕 f).toLp 2)]
    with t h₁ h₂ h₃
  rw [h₁, h₃, h₂]
  exact fourier_postcomp b f t

/-- Fourier transformation commutes with every constant operator. -/
theorem fourier_regularConstantHom (b : H →L[ℂ] H) (f : RegularCoreHilbert H) :
    (𝓕 (regularConstantHom volume b f) : RegularCoreHilbert H) =
      regularConstantHom volume b (𝓕 f) := by
  let F : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := Lp.fourierTransformₗᵢ ℝ H
  have he : F.comp (regularConstantHom volume b) = (regularConstantHom volume b).comp F := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
      (p := 2) ENNReal.ofNat_ne_top).equalizer
      (F.comp (regularConstantHom volume b)).continuous
      ((regularConstantHom volume b).comp F).continuous
    funext g
    exact fourier_constant_schwartz b g
  exact congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f) he

omit [CompleteSpace H] in
private theorem translate_toLp (s : ℝ) (f : SchwartzMap ℝ H) :
    (SchwartzMap.compSubConstCLM ℂ (-s) f).toLp 2 = regularTranslateApply s (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(SchwartzMap.compSubConstCLM ℂ (-s) f).coeFn_toLp 2,
    regularTranslateApply_ae s (f.toLp 2),
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae_eq_comp (f.coeFn_toLp 2)]
    with t h₁ h₂ h₃
  simp only [Function.comp_def] at h₃
  rw [h₁, h₂, h₃]
  simp only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]

private theorem fourier_translate_schwartz (s : ℝ) (f : SchwartzMap ℝ H) :
    (𝓕 (regularTranslateApply s (f.toLp 2)) : RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (𝓕 (f.toLp 2)) := by
  rw [← translate_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (SchwartzMap.compSubConstCLM ℂ (-s) f)).coeFn_toLp 2,
    (𝓕 f).coeFn_toLp 2, regularCharacterUnitary_apply_ae (2 * Real.pi * s) ((𝓕 f).toLp 2)]
    with t h₁ h₂ h₃
  rw [h₁, h₃, h₂, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have he : (SchwartzMap.compSubConstCLM ℂ (-s) f : ℝ → H) =
      (f : ℝ → H) ∘ (fun t => t + s) := by
    funext t
    simp only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, Function.comp_apply]
  rw [he]
  simp only [Real.fourier_real_eq]
  change Fourier.fourierIntegral Real.fourierChar volume ((f : ℝ → H) ∘ (fun t => t + s)) t = _
  rw [Fourier.fourierIntegral_comp_add_right]
  simp only [Fourier.fourierIntegral, VectorFourier.fourierIntegral, Circle.smul_def,
    Real.fourierChar_apply', regularCharacterScalar, mul_assoc]
  rfl

/-- Right translation becomes multiplication by the positive Fourier character. -/
theorem fourier_regularTranslateApply (s : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 (regularTranslateApply s f) : RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (𝓕 f) := by
  let F : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := Lp.fourierTransformₗᵢ ℝ H
  let R : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (regularTranslationEquiv (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  let C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  have he : F.comp R = C.comp F := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
      (p := 2) ENNReal.ofNat_ne_top).equalizer (F.comp R).continuous (C.comp F).continuous
    funext g
    exact fourier_translate_schwartz s g
  exact congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f) he

/-- Constant operators are unchanged by Fourier conjugation. -/
theorem fourierConj_regularConstantHom (b : H →L[ℂ] H) :
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv (regularConstantHom volume b) =
      regularConstantHom volume b := by
  apply ContinuousLinearMap.ext
  intro f
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change (𝓕 (regularConstantHom volume b ((Lp.fourierTransformₗᵢ ℝ H).symm f)) :
    RegularCoreHilbert H) = _
  rw [fourier_regularConstantHom]
  exact congrArg (regularConstantHom volume b) ((Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply f)

/-- Translation generators become the complete scalar-character family. -/
theorem fourierConj_regularTranslation (s : ℝ) :
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change (𝓕 (regularTranslateApply s ((Lp.fourierTransformₗᵢ ℝ H).symm f)) :
    RegularCoreHilbert H) = _
  rw [fourier_regularTranslateApply]
  exact congrArg
    (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    ((Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply f)

end

end KadisonKastler

end OAI
