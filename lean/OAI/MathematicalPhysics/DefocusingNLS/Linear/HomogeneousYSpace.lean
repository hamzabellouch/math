import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFourierMeasure
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! # The homogeneous space Y as a completed Fourier Hilbert space

The weighted L² model is complete. The radian Fourier image of Schwartz is
dense and injective, so this is precisely a completion of the Schwartz domain
with the homogeneous norm, rather than an added global L² requirement.
-/

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable abbrev HomogeneousY (a k : ℝ) := Lp ℂ 2 (homogeneousFourierMeasure a k)

noncomputable def radianFourierCLM : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((Units.mk0 ((2 * Real.pi)⁻¹) (by positivity)) • ContinuousLinearEquiv.refl ℝ E)).comp
    (SchwartzMap.fourierTransformCLM ℂ)

@[simp] theorem radianFourierCLM_apply (χ : 𝓢(E, ℂ)) :
    radianFourierCLM χ = radianFourierKernel χ := rfl

theorem radianFourierKernel_injective : Function.Injective radianFourierKernel := by
  intro χ ψ h
  let A : E ≃L[ℝ] E :=
    (Units.mk0 ((2 * Real.pi)⁻¹) (by positivity)) • ContinuousLinearEquiv.refl ℝ E
  have hF : 𝓕 χ = 𝓕 ψ := by
    ext ξ
    have he := congrArg (fun K : 𝓢(E, ℂ) => K (A.symm ξ)) h
    change (𝓕 χ) (A (A.symm ξ)) = (𝓕 ψ) (A (A.symm ξ)) at he
    simpa only [A.apply_symm_apply] using he
  have hi := congrArg (fun K : 𝓢(E, ℂ) => 𝓕⁻ K) hF
  simpa only [FourierTransform.fourierInv_fourier_eq] using hi

theorem radianFourierKernel_surjective : Function.Surjective radianFourierKernel := by
  intro K
  let A : E ≃L[ℝ] E :=
    (Units.mk0 ((2 * Real.pi)⁻¹) (by positivity)) • ContinuousLinearEquiv.refl ℝ E
  let ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm K
  refine ⟨𝓕⁻ ψ, ?_⟩
  ext ξ
  change (𝓕 (𝓕⁻ ψ)) (A ξ) = K ξ
  rw [FourierTransform.fourier_fourierInv_eq]
  change K (A.symm (A ξ)) = K ξ
  rw [A.symm_apply_apply]

noncomputable def homogeneousSchwartzEmbedding (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) : 𝓢(E, ℂ) →L[ℂ] HomogeneousY a k := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  exact (SchwartzMap.toLpCLM ℂ ℂ 2 (homogeneousFourierMeasure a k)).comp radianFourierCLM

@[simp] theorem homogeneousSchwartzEmbedding_apply (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ)) :
    let := homogeneousFourierMeasure_temperate a k ha ha1 hk
    homogeneousSchwartzEmbedding a k ha ha1 hk χ =
      (radianFourierKernel χ).toLp 2 (homogeneousFourierMeasure a k) := rfl

/-- The Schwartz Fourier domain is dense in the completed homogeneous space. -/
theorem homogeneousSchwartzEmbedding_dense (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    DenseRange (homogeneousSchwartzEmbedding a k ha ha1 hk) := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  let := homogeneousFourierMeasure_locallyFinite a k ha1 hk
  have hd := SchwartzMap.denseRange_toLpCLM (F := ℂ) (μ := homogeneousFourierMeasure a k)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  change DenseRange (fun K : 𝓢(E, ℂ) => K.toLp 2 (homogeneousFourierMeasure a k)) at hd
  exact hd.comp radianFourierKernel_surjective.denseRange (by fun_prop)

/-- No nonzero Schwartz function is identified with zero in this completion. -/
theorem homogeneousSchwartzEmbedding_injective (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    Function.Injective (homogeneousSchwartzEmbedding a k ha ha1 hk) := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  let := homogeneousFourierMeasure_openPos a k ha1 hk
  intro χ ψ h
  apply radianFourierKernel_injective
  exact SchwartzMap.injective_toLp 2 (homogeneousFourierMeasure a k) h

end DefocusingNLS

end OAI
