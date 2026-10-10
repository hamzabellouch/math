import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYNorm
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLocalizationBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEvaluation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierContinuity

namespace OAI

/-! # The actual localization operator into the homogeneous completion

The operator is the Fourier realization of χ(y/L)v(y). Its norm has a bound
independent of L ≥ 1, with the exact manuscript Y and Y_L norms.
-/

open MeasureTheory
open scoped SchwartzMap ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem norm_toLp_two_sq {f : E → ℂ} {μ : Measure E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 ∂μ := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]

theorem memLp_expandingPhysicalLocalization_fourier (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (f : FourierL2) :
    MemLp (radianFourierIntegral (expandingPhysicalLocalization a k L χ f)) 2
      (homogeneousFourierMeasure a k) := by
  have hc := continuous_radianFourierIntegral
    (integrable_expandingPhysicalLocalization a k L ha ha1 hk hL χ f)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  obtain ⟨C, hC, hb⟩ := exists_expandingPhysicalLocalization_bound a k ha ha1 hk χ
  have h := hb L hL f
  unfold homogeneousFourierMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    (continuous_homogeneousFourierWeight a k ha1 hk).measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hi := (h.1.add h.2.1).const_mul (((2 * Real.pi) ^ (12 : ℕ))⁻¹)
  convert hi using 1
  funext ξ
  rw [ENNReal.toReal_ofReal (homogeneousFourierWeight_nonneg a k ξ)]
  simp only [smul_eq_mul, homogeneousFourierWeight, Pi.add_apply]
  ring

/-- The Fourier representative of the actual physical localization. -/
noncomputable def homogeneousLocalization (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (f : FourierL2) : HomogeneousY a k :=
  (memLp_expandingPhysicalLocalization_fourier a k L ha ha1 hk hL χ f).toLp
    (radianFourierIntegral (expandingPhysicalLocalization a k L χ f))

theorem homogeneousLocalization_ae (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (f : FourierL2) :
    homogeneousLocalization a k L ha ha1 hk hL χ f =ᵐ[homogeneousFourierMeasure a k]
      radianFourierIntegral (expandingPhysicalLocalization a k L χ f) :=
  MemLp.coeFn_toLp _

theorem homogeneousLocalization_norm_sq (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (f : FourierL2) :
    ‖homogeneousLocalization a k L ha ha1 hk hL χ f‖ ^ 2 =
      ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        (homogeneousFourierEnergy (6 - a) (expandingPhysicalLocalization a k L χ f) +
          homogeneousFourierEnergy k (expandingPhysicalLocalization a k L χ f)) := by
  rw [homogeneousLocalization, norm_toLp_two_sq]
  obtain ⟨C, hC, hb⟩ := exists_expandingPhysicalLocalization_bound a k ha ha1 hk χ
  exact integral_homogeneousFourierMeasure a k ha1 hk _ (hb L hL f).1 (hb L hL f).2.1

private theorem expandingPhysicalLocalization_add (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (f g : FourierL2) :
    expandingPhysicalLocalization a k L χ (f + g) =
      expandingPhysicalLocalization a k L χ f + expandingPhysicalLocalization a k L χ g := by
  funext y
  simp only [expandingPhysicalLocalization,
    expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL, map_add, mul_add, Pi.add_apply]

private theorem expandingPhysicalLocalization_smul (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (c : ℂ) (f : FourierL2) :
    expandingPhysicalLocalization a k L χ (c • f) =
      c • expandingPhysicalLocalization a k L χ f := by
  funext y
  simp only [expandingPhysicalLocalization,
    expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL, map_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

noncomputable def homogeneousLocalizationLinearMap (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) : FourierL2 →ₗ[ℂ] HomogeneousY a k where
  toFun := homogeneousLocalization a k L ha ha1 hk hL χ
  map_add' f g := by
    have he : radianFourierIntegral (expandingPhysicalLocalization a k L χ (f + g)) =
        radianFourierIntegral (expandingPhysicalLocalization a k L χ f) +
          radianFourierIntegral (expandingPhysicalLocalization a k L χ g) := by
      rw [expandingPhysicalLocalization_add a k L ha ha1 hk hL,
        radianFourierIntegral_add
          (integrable_expandingPhysicalLocalization a k L ha ha1 hk hL χ f)
          (integrable_expandingPhysicalLocalization a k L ha ha1 hk hL χ g)]
    exact (MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_add _ _)
  map_smul' c f := by
    have he : radianFourierIntegral (expandingPhysicalLocalization a k L χ (c • f)) =
        c • radianFourierIntegral (expandingPhysicalLocalization a k L χ f) := by
      rw [expandingPhysicalLocalization_smul a k L ha ha1 hk hL,
        radianFourierIntegral_smul]
    exact (MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_const_smul _ _)

/-- One constant controls the actual localization operator on every expanding torus. -/
theorem exists_homogeneousLocalization_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (f : FourierL2),
      ‖homogeneousLocalization a k L ha ha1 hk hL χ f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hb⟩ := exists_expandingPhysicalLocalization_bound a k ha ha1 hk χ
  refine ⟨Real.sqrt (((2 * Real.pi) ^ (12 : ℕ))⁻¹ * C), Real.sqrt_nonneg _, ?_⟩
  intro L hL f
  have hs := mul_le_mul_of_nonneg_left (hb L hL f).2.2
    (show 0 ≤ ((2 * Real.pi) ^ (12 : ℕ))⁻¹ by positivity)
  rw [← homogeneousLocalization_norm_sq a k L ha ha1 hk hL χ f] at hs
  have hC' : 0 ≤ ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * C := by positivity
  have hsq := Real.sq_sqrt hC'
  have hroot := Real.sqrt_nonneg (((2 * Real.pi) ^ (12 : ℕ))⁻¹ * C)
  nlinarith [norm_nonneg (homogeneousLocalization a k L ha ha1 hk hL χ f), norm_nonneg f,
    mul_nonneg hroot (norm_nonneg f)]

noncomputable def homogeneousLocalizationCLM (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) : FourierL2 →L[ℂ] HomogeneousY a k :=
  (homogeneousLocalizationLinearMap a k L ha ha1 hk hL χ).mkContinuous
    (Classical.choose (exists_homogeneousLocalization_bound a k ha ha1 hk χ))
    ((Classical.choose_spec (exists_homogeneousLocalization_bound a k ha ha1 hk χ)).2 L hL)

@[simp] theorem homogeneousLocalizationCLM_apply (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (f : FourierL2) :
    homogeneousLocalizationCLM a k L ha ha1 hk hL χ f =
      homogeneousLocalization a k L ha ha1 hk hL χ f := rfl

end DefocusingNLS

end OAI
