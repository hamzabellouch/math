import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSchrodingerMultiplier
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeGroup

namespace OAI

/-! # The whole-space free group has the manuscript's physical-space formula -/

open MeasureTheory
open scoped SchwartzMap ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousPhysicalAmplitude (a b s : ℝ) : ℂ :=
  Complex.exp (((-a * s : ℝ) : ℂ) + Complex.I * ((b * s : ℝ) : ℂ))

theorem homogeneousPhysicalAmplitude_eq (a b s : ℝ) :
    homogeneousPhysicalAmplitude a b s =
      Complex.exp ((-(a : ℂ) + Complex.I * (b : ℂ)) * (s : ℂ)) := by
  unfold homogeneousPhysicalAmplitude
  congr 1
  push_cast
  ring_nf

@[simp] theorem homogeneousPhysicalAmplitude_norm (a b s : ℝ) :
    ‖homogeneousPhysicalAmplitude a b s‖ = Real.exp (-a * s) := by
  simp [homogeneousPhysicalAmplitude, Complex.norm_exp]

theorem homogeneousPhysicalCLM_rawSchwartz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) y =
      inverseRadianFourier ψ y := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  have he := (SchwartzMap.coeFn_toLp ψ 2 (homogeneousFourierMeasure a k)).filter_mono
    (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le
  exact congrFun (inverseRadianFourier_congr_ae he) y

theorem inverseRadianFourier_dilation (R : ℝ) (hR : 0 < R) (f : E → ℂ) (y : E) :
    inverseRadianFourier (fun ξ => f (R • ξ)) y =
      (((R⁻¹) ^ (12 : ℕ) : ℝ) : ℂ) * inverseRadianFourier f (R⁻¹ • y) := by
  have h := radianFourier_dilation R⁻¹ (inv_pos.mpr hR) f (-y)
  simp only [inv_inv, smul_neg] at h
  change radianFourierIntegral (fun ξ => f (R • ξ)) (-y) =
    (((R⁻¹) ^ (12 : ℕ) : ℝ) : ℂ) * radianFourierIntegral f (-(R⁻¹ • y)) at h
  unfold inverseRadianFourier
  rw [h]
  ring_nf

theorem homogeneousFreePhase_scaled (s : ℝ) (ξ : E) :
    homogeneousFreePhase s ξ =
      homogeneousSchrodingerPhase (1 - Real.exp (-s)) (Real.exp (s / 2) • ξ) := by
  unfold homogeneousFreePhase homogeneousSchrodingerPhase
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    ← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (s / 2) = s by ring_nf]
  have he : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
  have hreal : -(Real.exp s - 1) * ‖ξ‖ ^ 2 =
      -(1 - Real.exp (-s)) * (Real.exp s * ‖ξ‖ ^ 2) := by nlinarith
  exact congrArg (fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I)) hreal

theorem homogeneousFreeAmplitude_dilation (a b s : ℝ) :
    homogeneousFreeAmplitude a b s *
      (((Real.exp (s / 2))⁻¹ ^ (12 : ℕ) : ℝ) : ℂ) =
        homogeneousPhysicalAmplitude a b s := by
  have he : ((Real.exp (s / 2))⁻¹) ^ (12 : ℕ) = Real.exp (-6 * s) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    norm_num
    ring_nf
  rw [he, homogeneousFreeAmplitude, homogeneousPhysicalAmplitude, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

theorem inverseRadianFourier_homogeneousFree (a b s : ℝ) (ψ : 𝓢(E, ℂ)) (y : E) :
    inverseRadianFourier (homogeneousFreeFourier a b s ψ) y =
      homogeneousPhysicalAmplitude a b s *
        inverseRadianFourier
          (fun ξ => homogeneousSchrodingerPhase (1 - Real.exp (-s)) ξ * ψ ξ)
          (Real.exp (-s / 2) • y) := by
  have hf : (homogeneousFreeFourier a b s ψ : E → ℂ) =
      homogeneousFreeAmplitude a b s •
        (fun ξ => homogeneousSchrodingerPhase (1 - Real.exp (-s))
          (Real.exp (s / 2) • ξ) * ψ (Real.exp (s / 2) • ξ)) := by
    funext ξ
    rw [homogeneousFreeFourier_apply, homogeneousFreePhase_scaled]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring_nf
  rw [hf, inverseRadianFourier_smul]
  change homogeneousFreeAmplitude a b s * inverseRadianFourier
    (fun ξ => homogeneousSchrodingerPhase (1 - Real.exp (-s))
      (Real.exp (s / 2) • ξ) * ψ (Real.exp (s / 2) • ξ)) y = _
  rw [inverseRadianFourier_dilation _ (Real.exp_pos _)
    (fun ξ => homogeneousSchrodingerPhase (1 - Real.exp (-s)) ξ * ψ ξ) y]
  rw [← mul_assoc, homogeneousFreeAmplitude_dilation]
  congr 2
  rw [← Real.exp_neg]
  congr 1
  ring_nf

/-- Formula (lin:free-flow) on every element of the actual homogeneous completion. -/
theorem homogeneousFreeOperator_physical (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousFreeOperator a b k s ha ha1 hk f) y =
      homogeneousPhysicalAmplitude a b s *
        homogeneousPhysicalCLM a k ha ha1 hk
          (homogeneousSchrodingerOperator a k (1 - Real.exp (-s)) f)
          (Real.exp (-s / 2) • y) := by
  have hev (z : E) : Continuous (fun g : C₀(E, ℂ) => g z) :=
    (BoundedContinuousFunction.evalCLM ℂ z).continuous.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous
  have hleft : Continuous (fun f : HomogeneousY a k =>
      homogeneousPhysicalCLM a k ha ha1 hk (homogeneousFreeOperator a b k s ha ha1 hk f) y) :=
    ((hev y).comp
      (homogeneousPhysicalCLM a k ha ha1 hk).continuous).comp
        (homogeneousFreeOperator a b k s ha ha1 hk).continuous
  have hright : Continuous (fun f : HomogeneousY a k =>
      homogeneousPhysicalAmplitude a b s * homogeneousPhysicalCLM a k ha ha1 hk
        (homogeneousSchrodingerOperator a k (1 - Real.exp (-s)) f)
        (Real.exp (-s / 2) • y)) := by
    exact continuous_const.mul
      (((hev (Real.exp (-s / 2) • y)).comp
        (homogeneousPhysicalCLM a k ha ha1 hk).continuous).comp
          (homogeneousSchrodingerOperator a k (1 - Real.exp (-s))).continuous)
  have he := (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).equalizer hleft hright (by
    funext ψ
    simp only [Function.comp_apply, homogeneousFreeOperator_on_Schwartz,
      homogeneousSchrodingerOperator_Schwartz, homogeneousPhysicalCLM_rawSchwartz]
    rw [inverseRadianFourier_homogeneousFree]
    congr 2
    ext ξ
    exact (SchwartzMap.smulLeftCLM_apply_apply
      (homogeneousSchrodingerPhase_temperate (1 - Real.exp (-s))) ψ ξ).symm)
  exact congrFun he f

end DefocusingNLS

end OAI
