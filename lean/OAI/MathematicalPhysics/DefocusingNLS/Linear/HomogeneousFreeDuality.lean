import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFourierPairing
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreePhysical

namespace OAI

/-! # Exact Fourier-test action of the free similarity group

Changing variables moves the dilation onto the test function. This
identity holds on the whole homogeneous space by its dense Schwartz
realization and provides the distributional generator calculation.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousFreeDualTest (a b t : ℝ) (φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  homogeneousPhysicalAmplitude a b t •
    (SchwartzMap.smulLeftCLM ℂ (homogeneousSchrodingerPhase (1 - Real.exp (-t))))
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        ((Units.mk0 (Real.exp (-t / 2)) (Real.exp_ne_zero _)) •
          ContinuousLinearEquiv.refl ℝ E) φ)

theorem homogeneousFreeDualTest_apply (a b t : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    homogeneousFreeDualTest a b t φ ξ = homogeneousPhysicalAmplitude a b t *
      homogeneousSchrodingerPhase (1 - Real.exp (-t)) ξ *
        φ (Real.exp (-t / 2) • ξ) := by
  simp only [homogeneousFreeDualTest, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      (homogeneousSchrodingerPhase_temperate (1 - Real.exp (-t))),
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.smul_apply, ContinuousLinearEquiv.refl_apply,
    Units.val_mk0, smul_eq_mul]
  ring

theorem integral_homogeneousFreeFourier_dual (a b t : ℝ) (φ ψ : 𝓢(E, ℂ)) :
    (∫ ξ : E, homogeneousFreeFourier a b t ψ ξ * φ ξ) =
      ∫ ξ : E, ψ ξ * homogeneousFreeDualTest a b t φ ξ := by
  let R := Real.exp (t / 2)
  let g : E → ℂ := fun ξ =>
    ψ ξ * homogeneousSchrodingerPhase (1 - Real.exp (-t)) ξ * φ (R⁻¹ • ξ)
  have hR : 0 < R := Real.exp_pos _
  have hRinv : R⁻¹ = Real.exp (-t / 2) := by
    dsimp only [R]
    rw [← Real.exp_neg]
    congr 1
    ring
  have he (ξ : E) : homogeneousFreeFourier a b t ψ ξ * φ ξ =
      homogeneousFreeAmplitude a b t * g (R • ξ) := by
    rw [homogeneousFreeFourier_apply, homogeneousFreePhase_scaled]
    dsimp only [g, R]
    rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    ring
  calc
    (∫ ξ : E, homogeneousFreeFourier a b t ψ ξ * φ ξ) =
        homogeneousFreeAmplitude a b t * ∫ ξ : E, g (R • ξ) := by
      simp_rw [he]
      rw [integral_const_mul]
    _ = homogeneousFreeAmplitude a b t *
        (((R ^ (12 : ℕ))⁻¹ : ℝ) • ∫ ξ : E, g ξ) := by
      rw [Measure.integral_comp_smul_of_nonneg volume g R (hR := hR.le),
        finrank_euclideanSpace_fin]
    _ = homogeneousPhysicalAmplitude a b t * ∫ ξ : E, g ξ := by
      rw [Complex.real_smul, ← mul_assoc, ← inv_pow]
      rw [show homogeneousFreeAmplitude a b t * (((R⁻¹) ^ (12 : ℕ) : ℝ) : ℂ) =
        homogeneousPhysicalAmplitude a b t from homogeneousFreeAmplitude_dilation a b t]
    _ = ∫ ξ : E, ψ ξ * homogeneousFreeDualTest a b t φ ξ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun ξ => by
        dsimp only
        rw [homogeneousFreeDualTest_apply, ← hRinv]
        dsimp only [g]
        ring)

theorem homogeneousFreeOperator_fourier_duality (a b k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (φ : 𝓢(E, ℂ)) (u : HomogeneousY a k) :
    homogeneousFourierPairing a k ha ha1 hk φ
      (homogeneousFreeOperator a b k t ha ha1 hk u) =
      homogeneousFourierPairing a k ha ha1 hk (homogeneousFreeDualTest a b t φ) u := by
  have he := (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).equalizer
    (((homogeneousFourierPairing a k ha ha1 hk φ).comp
      (homogeneousFreeOperator a b k t ha ha1 hk)).continuous)
    (homogeneousFourierPairing a k ha ha1 hk (homogeneousFreeDualTest a b t φ)).continuous
    (by
      funext ψ
      simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
        homogeneousFreeOperator_on_Schwartz, homogeneousFourierPairing_Schwartz]
      exact integral_homogeneousFreeFourier_dual a b t φ ψ)
  exact congrFun he u

end DefocusingNLS

end OAI
