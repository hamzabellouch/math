import OAI.Analysis.KadisonKastler.FrequencyNest

namespace OAI

/-! # Fourier transforms of scalar character multipliers

The identity is established on Schwartz functions by the integral
formula, then on the actual `L²` space by density.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

local instance : NormedSpace ℝ ℂ := NormedSpace.complexToReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem character_eq_fourierChar (s t : ℝ) :
    regularCharacterScalar (2 * Real.pi * s) t = (Real.fourierChar (s * t) : ℂ) := by
  simp only [regularCharacterScalar, Real.fourierChar_apply', mul_assoc]

private theorem character_temperate (s : ℝ) :
    (regularCharacterScalar (2 * Real.pi * s)).HasTemperateGrowth := by
  change (fun t : ℝ => Complex.exp ((↑((2 * Real.pi * s) * t) : ℂ) * Complex.I)).HasTemperateGrowth
  exact Complex.hasTemperateGrowth_exp_mul_I.comp
    (f := fun t : ℝ => (2 * Real.pi * s) * t) (by fun_prop)

private def modulatedSchwartz (s : ℝ) (f : SchwartzMap ℝ H) : SchwartzMap ℝ H :=
  SchwartzMap.smulLeftCLM H (regularCharacterScalar (2 * Real.pi * s)) f

omit [CompleteSpace H] in
private theorem modulatedSchwartz_apply (s t : ℝ) (f : SchwartzMap ℝ H) :
    modulatedSchwartz s f t = regularCharacterScalar (2 * Real.pi * s) t • f t :=
  SchwartzMap.smulLeftCLM_apply_apply (character_temperate s) f t

private theorem modulatedSchwartz_toLp (s : ℝ) (f : SchwartzMap ℝ H) :
    (modulatedSchwartz s f).toLp 2 =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(modulatedSchwartz s f).coeFn_toLp 2, f.coeFn_toLp 2,
    regularCharacterUnitary_apply_ae (2 * Real.pi * s) (f.toLp 2)] with t h₁ h₂ h₃
  rw [h₁, h₃, h₂, modulatedSchwartz_apply]

omit [CompleteSpace H] in
private theorem fourier_modulate_function (s : ℝ) (f : ℝ → H) (x : ℝ) :
    𝓕 (fun t => regularCharacterScalar (2 * Real.pi * s) t • f t) x = 𝓕 f (x - s) := by
  simp only [Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [character_eq_fourierChar]
  simp only [Circle.smul_def, smul_smul]
  have he : -(t * x) + s * t = -(t * (x - s)) := by ring
  have hp := congrArg (fun z : Circle => (z : ℂ))
    (Real.fourierChar.map_add_eq_mul (-(t * x)) (s * t))
  rw [he] at hp
  simp only [Circle.coe_mul] at hp
  exact congrArg (fun z : ℂ => z • f t) hp.symm

private theorem fourier_modulate_schwartz (s : ℝ) (f : SchwartzMap ℝ H) :
    (𝓕 ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (f.toLp 2)) : RegularCoreHilbert H) =
    regularTranslateApply (-s) (𝓕 (f.toLp 2)) := by
  rw [← modulatedSchwartz_toLp, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (modulatedSchwartz s f)).coeFn_toLp 2,
    regularTranslateApply_ae (-s) ((𝓕 f).toLp 2),
    (measurePreserving_add_right volume (-s)).quasiMeasurePreserving.ae_eq_comp
      ((𝓕 f).coeFn_toLp 2)] with t h₁ h₂ h₃
  simp only [Function.comp_def] at h₃
  rw [h₁, h₂, h₃]
  rw [SchwartzMap.fourier_coe]
  have he : (modulatedSchwartz s f : ℝ → H) =
      fun t => regularCharacterScalar (2 * Real.pi * s) t • f t :=
    funext fun t => modulatedSchwartz_apply s t f
  rw [he]
  simpa only [sub_eq_add_neg, SchwartzMap.fourier_coe] using fourier_modulate_function s f t

/-- Multiplication by the scalar character translates Fourier frequency. -/
theorem fourier_regularCharacterUnitary (s : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) : RegularCoreHilbert H) =
    regularTranslateApply (-s) (𝓕 f) := by
  let F : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := Lp.fourierTransformₗᵢ ℝ H
  let T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := (regularTranslationEquiv (H := H) (-s) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  let C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularCharacterUnitary (H := H) (2 * Real.pi * s)
  have he : F.comp C = T.comp F := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
      (p := 2) ENNReal.ofNat_ne_top).equalizer
      (F.comp C).continuous (T.comp F).continuous
    funext g
    exact fourier_modulate_schwartz s g
  exact congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f) he

end

end KadisonKastler

end OAI
