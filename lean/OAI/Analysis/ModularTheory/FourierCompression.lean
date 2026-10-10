import OAI.Analysis.ModularTheory.FourierTranslation

namespace OAI

/-! Fourier transport of the scalar compression of the modular core. This
produces a unital completely positive contraction commuting with every
character multiplier. It does not postulate a core trace. -/

noncomputable section
open MeasureTheory FourierTransform

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

/-- The scalar inclusion in Fourier coordinates is an actual Hilbert-space
isometry, rather than a formal change of spectral variables. -/
def modularFourierInclusion : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ]
    Lp H 2 (volume : Measure ℝ) :=
  (modularScalarIsometry (volume : Measure ℝ) S).comp
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearIsometry

@[simp] lemma modularFourierInclusion_apply (f : Lp ℂ 2 (volume : Measure ℝ)) :
    modularFourierInclusion S f = modularScalarInclusion (volume : Measure ℝ) S (𝓕⁻ f) := rfl

lemma modularFourierInclusion_adjoint :
    (modularFourierInclusion S).toContinuousLinearMap.adjoint =
      (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (modularScalarExtraction (volume : Measure ℝ) S) := by
  change ((modularScalarInclusion (volume : Measure ℝ) S).comp
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap).adjoint = _
  rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm, ← modularScalarExtraction_adjoint]

/-- Scalar compression after Fourier diagonalization. -/
def modularFourierCompression : (Lp H 2 (volume : Measure ℝ) →L[ℂ]
    Lp H 2 (volume : Measure ℝ)) →L[ℂ]
      (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :=
  hilbertCompression (NonUnitalStarAlgHom.id ℂ _) (modularFourierInclusion S).toContinuousLinearMap

lemma modularFourierCompression_apply (T : Lp H 2 (volume : Measure ℝ) →L[ℂ]
    Lp H 2 (volume : Measure ℝ)) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    modularFourierCompression S T f =
      𝓕 (modularScalarCompression (volume : Measure ℝ) S T (𝓕⁻ f)) := by
  rw [modularFourierCompression, hilbertCompression_apply, modularFourierInclusion_adjoint]
  rfl

lemma modularFourierCompression_conjugate (T : Lp H 2 (volume : Measure ℝ) →L[ℂ]
    Lp H 2 (volume : Measure ℝ)) :
    modularFourierCompression S T = (Lp.fourierTransformₗᵢ ℝ ℂ).conjStarAlgEquiv
      (modularScalarCompression (volume : Measure ℝ) S T) := by
  apply ContinuousLinearMap.ext
  intro f
  exact modularFourierCompression_apply S T f

theorem modularFourierCompression_cp : CompletelyPositive (modularFourierCompression S) :=
  hilbertCompression_cp _ _

theorem modularFourierCompression_contractive : ‖modularFourierCompression S‖ ≤ 1 := by
  have hV : ‖(modularFourierInclusion S).toContinuousLinearMap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
      change ‖modularFourierInclusion S f‖ ≤ 1 * ‖f‖
      rw [(modularFourierInclusion S).norm_map, one_mul])
  exact (hilbertCompression_norm_le _ _).trans
    ((mul_le_mul hV hV (norm_nonneg (modularFourierInclusion S).toContinuousLinearMap)
      zero_le_one).trans_eq (one_mul 1))

@[simp] theorem modularFourierCompression_one : modularFourierCompression S 1 = 1 := by
  rw [modularFourierCompression_conjugate, modularScalarCompression_one, map_one]

lemma fourierConjugation_translation (s : ℝ) :
    (Lp.fourierTransformₗᵢ ℝ ℂ).conjStarAlgEquiv
      (modularLpTranslateEquiv (H := ℂ) (volume : Measure ℝ) s :
        Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) =
      (modularDualUnitary (H := ℂ) (volume : Measure ℝ) (-2 * Real.pi * s) :
        Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) := by
  apply ContinuousLinearMap.ext
  intro f
  change 𝓕 (modularLpTranslate (volume : Measure ℝ) s (𝓕⁻ f)) =
    modularDual (volume : Measure ℝ) (-2 * Real.pi * s) f
  rw [fourier_modularLpTranslate, fourier_fourierInv_eq]

/-- The Fourier compression of every core element commutes with every
character multiplier, including on the full von Neumann closure. -/
theorem modularFourierCompression_commutes (T : Lp H 2 (volume : Measure ℝ) →L[ℂ]
    Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S) (r : ℝ) :
    Commute (modularFourierCompression S T)
      (modularDualUnitary (H := ℂ) (volume : Measure ℝ) r :
        Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) := by
  let s := r / (-2 * Real.pi)
  have hs : -2 * Real.pi * s = r := by
    dsimp only [s]
    field_simp [Real.pi_ne_zero]
  have hc := (modularScalarCompression_commutes (volume : Measure ℝ) S T hT s).map
    (Lp.fourierTransformₗᵢ ℝ ℂ).conjStarAlgEquiv.toStarAlgHom
  change Commute ((Lp.fourierTransformₗᵢ ℝ ℂ).conjStarAlgEquiv
    (modularScalarCompression (volume : Measure ℝ) S T))
    ((Lp.fourierTransformₗᵢ ℝ ℂ).conjStarAlgEquiv
      (modularLpTranslateEquiv (H := ℂ) (volume : Measure ℝ) s :
        Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))) at hc
  rw [fourierConjugation_translation, hs, ← modularFourierCompression_conjugate] at hc
  exact hc

lemma modularScalarCompression_coefficient_translate (T : H →L[ℂ] H) (s : ℝ) :
    modularScalarCompression (volume : Measure ℝ) S
      (modularLpRepresentation volume S.D T *
        (modularLpTranslateEquiv (H := H) volume s :
          Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))) =
      inner ℂ S.xi (T S.xi) •
        (modularLpTranslateEquiv (H := ℂ) volume s :
          Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) := by
  apply ContinuousLinearMap.ext
  intro f
  change modularScalarExtraction volume S
    (modularLpRepresentation volume S.D T
      (modularLpTranslate volume s (modularScalarInclusion volume S f))) = _
  rw [← modularScalarInclusion_translate]
  change modularScalarCompression volume S (modularLpRepresentation volume S.D T)
    (modularLpTranslate volume s f) = _
  rw [modularScalarCompression_coefficient]
  rfl

/-- The Fourier coefficient of a crossed-product monomial is the original
vector-state coefficient times the corresponding character multiplier. -/
lemma modularFourierCompression_coefficient_translate (T : H →L[ℂ] H) (s : ℝ) :
    modularFourierCompression S
      (modularLpRepresentation volume S.D T *
        (modularLpTranslateEquiv (H := H) volume s :
          Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))) =
      inner ℂ S.xi (T S.xi) •
        (modularDualUnitary (H := ℂ) volume (-2 * Real.pi * s) :
          Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) := by
  rw [modularFourierCompression_conjugate,
    modularScalarCompression_coefficient_translate, map_smul,
    fourierConjugation_translation]

end WeakPureInfiniteness

end

end OAI
