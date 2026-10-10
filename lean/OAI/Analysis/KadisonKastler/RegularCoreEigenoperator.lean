import OAI.Analysis.KadisonKastler.RegularCoreCentralField

namespace OAI

/-! # Site eigenoperators become coefficient-weighted frequency shifts -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A scalar character becomes a frequency translation. -/
theorem fourierConj_regularCharacter (s : ℝ) :
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularRightTranslation (H := H) (Multiplicative.ofAdd (-s)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change (𝓕 ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) ((Lp.fourierTransformₗᵢ ℝ H).symm f)) :
      RegularCoreHilbert H) = _
  rw [fourier_regularCharacterUnitary]
  change regularTranslateApply (-s) (𝓕 ((Lp.fourierTransformₗᵢ ℝ H).symm f)) =
    regularTranslateApply (-s) f
  exact congrArg (regularTranslateApply (-s)) ((Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply f)

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

/-- The regular representation of an eigenoperator is a constant
coefficient followed by the associated character multiplier. -/
theorem regularCoreEmbedding_of_eigenoperator (b : H →L[ℂ] H) (s : ℝ)
    (heigen : ∀ t : ℝ, unitaryConj (star (U (Multiplicative.ofAdd t))) b =
      regularCharacterScalar (2 * Real.pi * s) t • b) :
    regularCoreEmbedding U hU b = regularConstantHom volume b *
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCoreEmbedding_apply_ae U hU b f,
    regularConstantHom_apply_ae volume b
      ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCharacterUnitary_apply_ae (2 * Real.pi * s) f] with t hp hc hm
  change regularCoreEmbedding U hU b f t =
    regularConstantHom volume b
      ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hp, hc, hm]
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp,
    smul_apply, map_smul] using
    congrArg (fun B : H →L[ℂ] H => B (f t)) (heigen t)

/-- After Fourier transform, the eigenoperator is a coefficient-weighted
translation. This is the shift used in the factorial-core argument. -/
theorem fourierConj_regularCoreEigenoperator (b : H →L[ℂ] H) (s : ℝ)
    (heigen : ∀ t : ℝ, unitaryConj (star (U (Multiplicative.ofAdd t))) b =
      regularCharacterScalar (2 * Real.pi * s) t • b) :
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv (regularCoreEmbedding U hU b) =
      regularConstantHom volume b *
        (regularRightTranslation (H := H) (Multiplicative.ofAdd (-s)) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  rw [regularCoreEmbedding_of_eigenoperator U hU b s heigen, map_mul,
    fourierConj_regularConstantHom, fourierConj_regularCharacter]

end

end KadisonKastler

end OAI
