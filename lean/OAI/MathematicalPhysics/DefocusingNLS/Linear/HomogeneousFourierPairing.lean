import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalMap
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeOperator

namespace OAI

/-! # Bounded Fourier test functionals on the actual homogeneous space

The inverse weight makes every Y vector an integrable Fourier function.
Consequently Schwartz tests act continuously on Y, with their ordinary
Lebesgue pairing, rather than an unspecified distributional realization.
-/

open MeasureTheory
open scoped SchwartzMap ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

section

variable (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)

include ha ha1 hk

theorem homogeneousFourier_integral_norm_le (f : HomogeneousY a k) :
    (∫ ξ : E, ‖f ξ‖) ≤
      Real.sqrt (∫ ξ : E, (homogeneousFourierWeight a k ξ)⁻¹) * ‖f‖ := by
  have hn : Real.sqrt (∫ ξ, ‖f ξ‖ ^ 2 ∂homogeneousFourierMeasure a k) = ‖f‖ := by
    rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num
  simpa only [hn] using
    (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp f)).2

theorem integrable_homogeneousFourier_test (f : HomogeneousY a k) (φ : 𝓢(E, ℂ)) :
    Integrable (fun ξ : E => f ξ * φ ξ) :=
  (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp f)).1.mul_bdd
    φ.continuous.aestronglyMeasurable (ae_of_all _ (φ.norm_le_seminorm ℂ))

noncomputable def homogeneousFourierPairing (φ : 𝓢(E, ℂ)) : HomogeneousY a k →L[ℂ] ℂ := by
  let L : HomogeneousY a k →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ ξ : E, f ξ * φ ξ
      map_add' := by
        intro f g
        calc
          (∫ ξ : E, (f + g) ξ * φ ξ) =
              ∫ ξ : E, (f ξ * φ ξ + g ξ * φ ξ) := by
            apply integral_congr_ae
            filter_upwards [(Lp.coeFn_add f g).filter_mono
              (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le]
              with ξ hξ
            rw [hξ, Pi.add_apply, add_mul]
          _ = _ := integral_add
            (integrable_homogeneousFourier_test a k ha ha1 hk f φ)
            (integrable_homogeneousFourier_test a k ha ha1 hk g φ)
      map_smul' := by
        intro c f
        calc
          (∫ ξ : E, (c • f) ξ * φ ξ) = ∫ ξ : E, c * (f ξ * φ ξ) := by
            apply integral_congr_ae
            filter_upwards [(Lp.coeFn_smul c f).filter_mono
              (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le]
              with ξ hξ
            rw [hξ, Pi.smul_apply, smul_eq_mul, mul_assoc]
          _ = c • ∫ ξ : E, f ξ * φ ξ := by rw [integral_const_mul, smul_eq_mul] }
  refine L.mkContinuous
    ((SchwartzMap.seminorm ℂ 0 0 φ) *
      Real.sqrt (∫ ξ : E, (homogeneousFourierWeight a k ξ)⁻¹)) ?_
  intro f
  have hnorm := norm_integral_le_integral_norm (μ := volume) (fun ξ : E => f ξ * φ ξ)
  have hpoint : (∫ ξ : E, ‖f ξ * φ ξ‖) ≤
      (SchwartzMap.seminorm ℂ 0 0 φ) * ∫ ξ : E, ‖f ξ‖ := by
    rw [← integral_const_mul]
    apply integral_mono
      (integrable_homogeneousFourier_test a k ha ha1 hk f φ).norm
      ((integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp f)).1.norm.const_mul _)
    intro ξ
    dsimp only
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (φ.norm_le_seminorm ℂ ξ) (norm_nonneg _)).trans_eq
      (mul_comm _ _)
  exact hnorm.trans (hpoint.trans ((mul_le_mul_of_nonneg_left
    (homogeneousFourier_integral_norm_le a k ha ha1 hk f) (apply_nonneg _ _)).trans_eq
      (mul_assoc _ _ _).symm))

@[simp] theorem homogeneousFourierPairing_apply (φ : 𝓢(E, ℂ)) (f : HomogeneousY a k) :
    homogeneousFourierPairing a k ha ha1 hk φ f = ∫ ξ : E, f ξ * φ ξ := rfl

theorem homogeneousFourierPairing_Schwartz (φ ψ : 𝓢(E, ℂ)) :
    homogeneousFourierPairing a k ha ha1 hk φ
      (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) = ∫ ξ : E, ψ ξ * φ ξ := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  apply integral_congr_ae
  filter_upwards [(SchwartzMap.coeFn_toLp ψ 2 (homogeneousFourierMeasure a k)).filter_mono
    (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le] with ξ hξ
  exact congrArg (fun z : ℂ => z * φ ξ) hξ

end

end DefocusingNLS

end OAI
