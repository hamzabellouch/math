import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreePhysical

namespace OAI

/-! # Exact homogeneous scaling for the dyadic profile-membership estimate -/

open MeasureTheory
open scoped SchwartzMap ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousFourierDilation (a R : ℝ) (hR : 0 < R) :
    𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  ((R ^ (12 - 2 * a) : ℝ) : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((Units.mk0 R hR.ne') • ContinuousLinearEquiv.refl ℝ E)

@[simp] theorem homogeneousFourierDilation_apply (a R : ℝ) (hR : 0 < R)
    (ψ : 𝓢(E, ℂ)) (ξ : E) :
    homogeneousFourierDilation a R hR ψ ξ = (R ^ (12 - 2 * a) : ℝ) * ψ (R • ξ) := by
  simp [homogeneousFourierDilation]

theorem homogeneousFourierDilation_energy (a R s : ℝ) (hR : 0 < R) (ψ : 𝓢(E, ℂ)) :
    homogeneousFrequencyEnergy s (homogeneousFourierDilation a R hR ψ) =
      R ^ (12 - 4 * a - 2 * s) * homogeneousFrequencyEnergy s ψ := by
  have he : (homogeneousFourierDilation a R hR ψ : E → ℂ) =
      fun ξ => ((R ^ (12 - 2 * a) : ℝ) : ℂ) * ψ (R • ξ) := by
    funext ξ
    exact homogeneousFourierDilation_apply a R hR ψ ξ
  rw [he]
  have hn (ξ : E) : ‖((R ^ (12 - 2 * a) : ℝ) : ℂ) * ψ (R • ξ)‖ ^ 2 =
      (R ^ (12 - 2 * a)) ^ 2 * ‖ψ (R • ξ)‖ ^ 2 := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hR.le _), mul_pow]
  have hi (ξ : E) :
      ‖ξ‖ ^ (2 * s) * ‖((R ^ (12 - 2 * a) : ℝ) : ℂ) * ψ (R • ξ)‖ ^ 2 =
        (R ^ (12 - 2 * a)) ^ 2 * (‖ξ‖ ^ (2 * s) * ‖ψ (R • ξ)‖ ^ 2) := by
    rw [hn]
    ring
  change (∫ ξ, ‖ξ‖ ^ (2 * s) * ‖((R ^ (12 - 2 * a) : ℝ) : ℂ) * ψ (R • ξ)‖ ^ 2) = _
  simp_rw [hi]
  rw [integral_const_mul]
  change (R ^ (12 - 2 * a)) ^ 2 * homogeneousFrequencyEnergy s (fun ξ => ψ (R • ξ)) = _
  rw [homogeneousFrequencyEnergy_dilation s R hR, ← Real.rpow_natCast,
    ← Real.rpow_mul hR.le, ← mul_assoc, ← Real.rpow_add hR]
  congr 2
  norm_num
  ring

theorem homogeneousFourierDilation_norm_le (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R) (ψ : 𝓢(E, ℂ)) :
    ‖homogeneousFrequencyEmbedding a k ha ha1 hk
        (homogeneousFourierDilation a R (by linarith) ψ)‖ ≤
      R ^ (-a) * ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖ := by
  have hRp : 0 < R := by linarith
  have hhigh : R ^ (12 - 4 * a - 2 * k) ≤ R ^ (-2 * a) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hlow : 12 - 4 * a - 2 * (6 - a) = -2 * a := by ring
  have hsq : (R ^ (-a)) ^ 2 = R ^ (-2 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hRp.le]
    congr 1
    norm_num
    ring
  have hsquare :
      ‖homogeneousFrequencyEmbedding a k ha ha1 hk
          (homogeneousFourierDilation a R hRp ψ)‖ ^ 2 ≤
        (R ^ (-a) * ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖) ^ 2 := by
    rw [homogeneousFrequencyEmbedding_norm_sq, homogeneousFourierDilation_energy,
      homogeneousFourierDilation_energy, hlow]
    conv_rhs => rw [mul_pow, hsq, homogeneousFrequencyEmbedding_norm_sq]
    have hp : 0 ≤ homogeneousFrequencyEnergy k ψ := integral_nonneg (fun _ => by positivity)
    have hc : 0 ≤ ((2 * Real.pi) ^ (12 : ℕ))⁻¹ := by positivity
    calc
      _ ≤ ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
          (R ^ (-2 * a) * homogeneousFrequencyEnergy (6 - a) ψ +
            R ^ (-2 * a) * homogeneousFrequencyEnergy k ψ) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right hhigh hp)) hc
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hRp.le _) (norm_nonneg _))).mp hsquare

noncomputable def homogeneousDilation (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R) :
    HomogeneousY a k →L[ℂ] HomogeneousY a k :=
  ((homogeneousFrequencyEmbedding a k ha ha1 hk).comp
    (homogeneousFourierDilation a R (by linarith))).toLinearMap.extendOfNorm
      (homogeneousFrequencyEmbedding a k ha ha1 hk).toLinearMap

theorem homogeneousDilation_on_Schwartz (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R) (ψ : 𝓢(E, ℂ)) :
    homogeneousDilation a k R ha ha1 hk hR (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) =
      homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousFourierDilation a R (by linarith) ψ) :=
  LinearMap.extendOfNorm_eq (homogeneousFrequencyEmbedding_dense a k ha ha1 hk)
    ⟨R ^ (-a), homogeneousFourierDilation_norm_le a k R ha ha1 hk hR⟩ ψ

theorem homogeneousDilation_norm_le (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R) (f : HomogeneousY a k) :
    ‖homogeneousDilation a k R ha ha1 hk hR f‖ ≤ R ^ (-a) * ‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le (homogeneousFrequencyEmbedding_dense a k ha ha1 hk)
    (R ^ (-a)) (homogeneousFourierDilation_norm_le a k R ha ha1 hk hR) f

theorem inverseRadianFourier_homogeneousDilation (a R : ℝ) (hR : 0 < R)
    (ψ : 𝓢(E, ℂ)) (y : E) :
    inverseRadianFourier (homogeneousFourierDilation a R hR ψ) y =
      (R ^ (-2 * a) : ℝ) * inverseRadianFourier ψ (R⁻¹ • y) := by
  have he : (homogeneousFourierDilation a R hR ψ : E → ℂ) =
      ((R ^ (12 - 2 * a) : ℝ) : ℂ) • (fun ξ => ψ (R • ξ)) := by
    funext ξ
    exact homogeneousFourierDilation_apply a R hR ψ ξ
  rw [he, inverseRadianFourier_smul]
  change ((R ^ (12 - 2 * a) : ℝ) : ℂ) * inverseRadianFourier (fun ξ => ψ (R • ξ)) y = _
  rw [inverseRadianFourier_dilation R hR, ← mul_assoc, ← Complex.ofReal_mul]
  have hc : R ^ (12 - 2 * a) * (R⁻¹) ^ (12 : ℕ) = R ^ (-2 * a) := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hR.le, ← Real.rpow_add hR]
    congr 1
    norm_num
    ring
  rw [hc]

/-- The operator is exactly the physical scaling `R^(-2a) f(y/R)`. -/
theorem homogeneousDilation_physical (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R)
    (f : HomogeneousY a k) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousDilation a k R ha ha1 hk hR f) y =
      (R ^ (-2 * a) : ℝ) * homogeneousPhysicalCLM a k ha ha1 hk f (R⁻¹ • y) := by
  have hev (z : E) : Continuous (fun h : C₀(E, ℂ) => h z) :=
    (BoundedContinuousFunction.evalCLM ℂ z).continuous.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous
  have hl := ((hev y).comp (homogeneousPhysicalCLM a k ha ha1 hk).continuous).comp
    (homogeneousDilation a k R ha ha1 hk hR).continuous
  have hr : Continuous (fun f : HomogeneousY a k =>
      ((R ^ (-2 * a) : ℝ) : ℂ) * homogeneousPhysicalCLM a k ha ha1 hk f (R⁻¹ • y)) :=
    continuous_const.mul ((hev (R⁻¹ • y)).comp (homogeneousPhysicalCLM a k ha ha1 hk).continuous)
  have he := (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).equalizer hl hr (by
    funext ψ
    change homogeneousPhysicalCLM a k ha ha1 hk
      (homogeneousDilation a k R ha ha1 hk hR (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)) y =
        ((R ^ (-2 * a) : ℝ) : ℂ) * homogeneousPhysicalCLM a k ha ha1 hk
          (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) (R⁻¹ • y)
    rw [homogeneousDilation_on_Schwartz, homogeneousPhysicalCLM_rawSchwartz,
      homogeneousPhysicalCLM_rawSchwartz]
    exact inverseRadianFourier_homogeneousDilation a R (by linarith) ψ y)
  exact congrFun he f

end DefocusingNLS

end OAI
