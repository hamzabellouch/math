import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFourierL1
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierContinuity
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

namespace OAI

/-! # Actual continuous functions represented by the homogeneous space

Every Y vector has an integrable Fourier representative. Its inverse Fourier
integral is continuous, vanishes at infinity, and obeys a uniform norm bound.
-/

open Filter MeasureTheory Topology
open scoped ENNReal FourierTransform SchwartzMap ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def inverseRadianFourier (f : E → ℂ) (y : E) : ℂ :=
  (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) * radianFourierIntegral f (-y)

theorem continuous_inverseRadianFourier {f : E → ℂ} (hf : Integrable f) :
    Continuous (inverseRadianFourier f) :=
  continuous_const.mul ((continuous_radianFourierIntegral hf).comp continuous_neg)

theorem zero_at_infty_inverseRadianFourier (f : E → ℂ) :
    Tendsto (inverseRadianFourier f) (cocompact E) (𝓝 0) := by
  let A : E ≃L[ℝ] E :=
    (Units.mk0 (-(2 * Real.pi)⁻¹) (neg_ne_zero.mpr (inv_ne_zero (by positivity)))) • ContinuousLinearEquiv.refl ℝ E
  have hF : Tendsto (𝓕 f) (cocompact E) (𝓝 0) :=
    tendsto_integral_exp_inner_smul_cocompact f
  have ht := hF.comp A.toHomeomorph.toCocompactMap.cocompact_tendsto'
  change Tendsto (fun y => (𝓕 f) (A y)) (cocompact E) (𝓝 0) at ht
  have he (y : E) : radianFourierIntegral f (-y) = (𝓕 f) (A y) := by
    rw [radianFourierIntegral_eq_fourier]
    simp only [A, ContinuousLinearEquiv.smul_apply, ContinuousLinearEquiv.refl_apply,
      Units.val_mk0, neg_smul, smul_neg]
  have heq : inverseRadianFourier f = fun y =>
      ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) * (𝓕 f) (A y) := by
    funext y
    exact congrArg (fun z : ℂ => (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) * z) (he y)
  rw [heq]
  simpa only [mul_zero] using ht.const_mul ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ)

theorem inverseRadianFourier_norm_le (f : E → ℂ) (y : E) :
    ‖inverseRadianFourier f y‖ ≤ ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * ∫ ξ, ‖f ξ‖ := by
  rw [inverseRadianFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold radianFourierIntegral
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1
  funext ξ
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The inverse Fourier normalization recovers every Schwartz function exactly. -/
theorem inverseRadianFourier_kernel (χ : 𝓢(E, ℂ)) (y : E) :
    inverseRadianFourier (radianFourierKernel χ) y = χ y := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hi : (𝓕 (𝓕 χ : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) (-y) = χ y := by
    have h := congrArg (fun ψ : 𝓢(E, ℂ) => ψ y)
      (FourierTransform.fourierInv_fourier_eq (F := 𝓢(E, ℂ)) χ)
    exact h
  change (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) *
    radianFourierIntegral (fun ξ => (𝓕 χ) ((2 * Real.pi)⁻¹ • ξ)) (-y) = χ y
  rw [radianFourier_dilation (2 * Real.pi) hp, radianFourierIntegral_eq_fourier]
  simp only [smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  have hi' : (𝓕 ((𝓕 χ : 𝓢(E, ℂ)) : E → ℂ)) (-y) = χ y := hi
  rw [hi']
  change ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) *
    ((((2 * Real.pi) ^ (12 : ℕ) : ℝ) : ℂ) * χ y) = χ y
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 12 hp.ne'),
    Complex.ofReal_one, one_mul]

noncomputable def homogeneousPhysicalFunction (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) : C₀(E, ℂ) where
  toFun := inverseRadianFourier f
  continuous_toFun := continuous_inverseRadianFourier
    (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp f)).1
  zero_at_infty' := zero_at_infty_inverseRadianFourier f

@[simp] theorem homogeneousPhysicalFunction_apply (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) (y : E) :
    homogeneousPhysicalFunction a k ha ha1 hk f y = inverseRadianFourier f y := rfl

/-- Whole-space point observation has one finite constant determined by the exact weight. -/
theorem homogeneousPhysicalFunction_norm_le (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    ‖homogeneousPhysicalFunction a k ha ha1 hk f‖ ≤
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        Real.sqrt (∫ ξ, (homogeneousFourierWeight a k ξ)⁻¹)) * ‖f‖ := by
  have hn : Real.sqrt (∫ ξ, ‖f ξ‖ ^ 2 ∂homogeneousFourierMeasure a k) = ‖f‖ := by
    rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num
  have hl1 := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp f)).2
  rw [hn] at hl1
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro y
  exact (inverseRadianFourier_norm_le f y).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl1
      (show 0 ≤ ((2 * Real.pi) ^ (12 : ℕ))⁻¹ by positivity))

end DefocusingNLS

end OAI
