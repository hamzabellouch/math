import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalMap
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace OAI

/-! # Faithfulness of the physical homogeneous realization

The inverse Fourier realization is injective. The proof uses Fourier duality
against Schwartz tests and the fundamental lemma for locally integrable functions.
-/

open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem integral_fourier_mul_schwartz {f : E → ℂ}
    (hf : Integrable f) (g : 𝓢(E, ℂ)) :
    (∫ ξ, 𝓕 f ξ * g ξ) = ∫ ξ, f ξ * (𝓕 g) ξ := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ E)
    Real.continuous_fourierChar continuous_inner hf g.integrable

private theorem ae_eq_zero_of_fourier_zero {f : E → ℂ} (hf : Integrable f)
    (hF : ∀ ξ, 𝓕 f ξ = 0) : f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hgc
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hs : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let χ : 𝓢(E, ℂ) := hc.toSchwartzMap hs
  have h := integral_fourier_mul_schwartz hf (𝓕⁻ χ)
  simp only [hF, zero_mul, integral_zero, FourierTransform.fourier_fourierInv_eq] at h
  change (∫ ξ, (g ξ : ℂ) * f ξ) = 0
  calc
    _ = ∫ ξ, f ξ * χ ξ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      change (g ξ : ℂ) * f ξ = f ξ * (g ξ : ℂ)
      ring
    _ = 0 := h.symm

private theorem ae_eq_zero_of_inverseRadian_zero {f : E → ℂ} (hf : Integrable f)
    (hF : ∀ y, inverseRadianFourier f y = 0) : f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_fourier_zero hf
  intro ξ
  have h := hF (-((2 * Real.pi) • ξ))
  simp only [inverseRadianFourier, neg_neg, radianFourierIntegral_eq_fourier,
    smul_smul, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast inv_ne_zero (pow_ne_zero 12
    (by positivity : 2 * Real.pi ≠ 0)))

/-- Equality of inverse Fourier transforms determines integrable Fourier data. -/
theorem inverseRadianFourier_injective_ae {f g : E → ℂ}
    (hf : Integrable f) (hg : Integrable g)
    (h : inverseRadianFourier f = inverseRadianFourier g) : f =ᵐ[volume] g := by
  have hz : f - g =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_inverseRadian_zero (hf.sub hg)
    intro y
    have he : inverseRadianFourier (f - g) =
        inverseRadianFourier f - inverseRadianFourier g := by
      have hn := inverseRadianFourier_smul (-1) g
      have ha := inverseRadianFourier_add hf (hg.smul (-1 : ℂ))
      simpa only [neg_one_smul, sub_eq_add_neg] using ha.trans
        (congrArg (fun F => inverseRadianFourier f + F) hn)
    rw [he, h, sub_self]
    rfl
  filter_upwards [hz] with ξ hξ
  exact sub_eq_zero.mp hξ

/-- Distinct Y vectors represent distinct continuous functions. -/
theorem homogeneousPhysicalCLM_injective (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    Function.Injective (homogeneousPhysicalCLM a k ha ha1 hk) := by
  apply (injective_iff_map_eq_zero (homogeneousPhysicalCLM a k ha ha1 hk)).mpr
  intro f hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have hzero : (f : E → ℂ) =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_inverseRadian_zero
      (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp f)).1
    intro y
    exact DFunLike.congr_fun hf y
  exact hzero.filter_mono (withDensity_absolutelyContinuous volume _).ae_le

end DefocusingNLS

end OAI
