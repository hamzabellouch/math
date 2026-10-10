import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCZero

namespace OAI

/-! # Bounded linear physical realization of the homogeneous space

Almost-everywhere arithmetic of the Fourier representatives becomes exact
arithmetic of the inverse Fourier functions.
-/

open MeasureTheory
open scoped SchwartzMap ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem volume_absolutelyContinuous_homogeneousFourierMeasure (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) : volume ≪ homogeneousFourierMeasure a k := by
  apply withDensity_absolutelyContinuous'
    (continuous_homogeneousFourierWeight a k ha1 hk).measurable.ennreal_ofReal.aemeasurable
  have hn : ∀ᵐ ξ : E ∂volume, ξ ≠ 0 := by
    simp only [ae_iff, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton _
  filter_upwards [hn] with ξ hξ
  exact (ENNReal.ofReal_pos.mpr (homogeneousFourierWeight_pos a k ξ hξ)).ne'

theorem inverseRadianFourier_congr_ae {f g : E → ℂ} (h : f =ᵐ[volume] g) :
    inverseRadianFourier f = inverseRadianFourier g := by
  funext y
  simp only [inverseRadianFourier, radianFourierIntegral_eq_fourier,
    Real.fourier_congr_ae h]

theorem inverseRadianFourier_add {f g : E → ℂ} (hf : Integrable f) (hg : Integrable g) :
    inverseRadianFourier (f + g) = inverseRadianFourier f + inverseRadianFourier g := by
  funext y
  simp only [inverseRadianFourier, radianFourierIntegral_add hf hg, Pi.add_apply, mul_add]

theorem inverseRadianFourier_smul (c : ℂ) (f : E → ℂ) :
    inverseRadianFourier (c • f) = c • inverseRadianFourier f := by
  funext y
  simp only [inverseRadianFourier, radianFourierIntegral_smul, Pi.smul_apply, smul_eq_mul]
  ring

noncomputable def homogeneousPhysicalLinearMap (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) : HomogeneousY a k →ₗ[ℂ] C₀(E, ℂ) where
  toFun := homogeneousPhysicalFunction a k ha ha1 hk
  map_add' f g := by
    apply DFunLike.ext
    intro y
    have hfg : ((f + g : HomogeneousY a k) : E → ℂ) =ᵐ[volume]
        (fun ξ => f ξ + g ξ) := (Lp.coeFn_add f g).filter_mono
      (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le
    have he := inverseRadianFourier_congr_ae hfg
    change inverseRadianFourier (f + g : HomogeneousY a k) =
      inverseRadianFourier ((f : E → ℂ) + (g : E → ℂ)) at he
    rw [inverseRadianFourier_add
      (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp f)).1
      (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp g)).1] at he
    exact congrFun he y
  map_smul' c f := by
    apply DFunLike.ext
    intro y
    have hcf : ((c • f : HomogeneousY a k) : E → ℂ) =ᵐ[volume]
        (fun ξ => c • f ξ) := (Lp.coeFn_smul c f).filter_mono
      (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le
    have he := inverseRadianFourier_congr_ae hcf
    change inverseRadianFourier (c • f : HomogeneousY a k) =
      inverseRadianFourier (c • (f : E → ℂ)) at he
    rw [inverseRadianFourier_smul] at he
    exact congrFun he y

noncomputable def homogeneousPhysicalCLM (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) : HomogeneousY a k →L[ℂ] C₀(E, ℂ) :=
  (homogeneousPhysicalLinearMap a k ha ha1 hk).mkContinuous
    (((2 * Real.pi) ^ (12 : ℕ))⁻¹ * Real.sqrt (∫ ξ, (homogeneousFourierWeight a k ξ)⁻¹))
    (homogeneousPhysicalFunction_norm_le a k ha ha1 hk)

@[simp] theorem homogeneousPhysicalCLM_apply (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    homogeneousPhysicalCLM a k ha ha1 hk f = homogeneousPhysicalFunction a k ha ha1 hk f := rfl

/-- The physical map agrees with the original Schwartz function on the dense domain. -/
theorem homogeneousPhysicalCLM_Schwartz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ)) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousSchwartzEmbedding a k ha ha1 hk χ) y =
      χ y := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  have he : (homogeneousSchwartzEmbedding a k ha ha1 hk χ : E → ℂ) =ᵐ[volume]
      radianFourierKernel χ := by
    rw [homogeneousSchwartzEmbedding_apply]
    exact (SchwartzMap.coeFn_toLp _ _ _).filter_mono
      (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le
  change inverseRadianFourier (homogeneousSchwartzEmbedding a k ha ha1 hk χ) y = χ y
  rw [inverseRadianFourier_congr_ae he, inverseRadianFourier_kernel]

end DefocusingNLS

end OAI
