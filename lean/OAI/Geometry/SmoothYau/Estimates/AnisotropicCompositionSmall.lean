import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ContDiffPartialIteratedFDeriv
import OAI.Geometry.SmoothYau.Smoothness.MomentBesselLp

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
section Neumann
variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

def neumannCorrectedInverse (R : Y →L[𝕜] X) (P : X →L[𝕜] Y) (h : ‖R ∘L P‖ < 1) :
    Y →L[𝕜] X :=
  let hb := ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_one_sub_of_norm_lt_one h)
  (ContinuousLinearEquiv.ofBijective (1 - R ∘L P)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)).symm.toContinuousLinearMap ∘L R

lemma neumannCorrectedInverse_fixed (R : Y →L[𝕜] X) (P : X →L[𝕜] Y)
    (h : ‖R ∘L P‖ < 1) (f : Y) :
    neumannCorrectedInverse R P h f = R (f + P (neumannCorrectedInverse R P h f)) := by
  let hb := ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_one_sub_of_norm_lt_one h)
  let e := ContinuousLinearEquiv.ofBijective (1 - R ∘L P)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have he := e.apply_symm_apply (R f)
  change neumannCorrectedInverse R P h f - R (P (neumannCorrectedInverse R P h f)) = R f at he
  rw [map_add]
  exact sub_eq_iff_eq_add.mp he

lemma neumannCorrectedInverse_bound (R : Y →L[𝕜] X) (P : X →L[𝕜] Y)
    (h : ‖R ∘L P‖ < 1) (C : ℝ) (hR : ‖R‖ ≤ C) (hq : C * ‖P‖ ≤ 1 / 2) (f : Y) :
    ‖neumannCorrectedInverse R P h f‖ ≤ 2 * C * ‖f‖ := by
  have hC := (norm_nonneg R).trans hR
  let u := neumannCorrectedInverse R P h f
  have hu : ‖u‖ ≤ C * (‖f‖ + ‖P‖ * ‖u‖) := by
    conv_lhs => rw [show u = R (f + P u) from neumannCorrectedInverse_fixed R P h f]
    exact (R.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hR (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
        (add_le_add le_rfl (P.le_opNorm u))) hC))
  have hp := mul_le_mul_of_nonneg_right hq (norm_nonneg u)
  dsimp only [u] at hu hp
  nlinarith

lemma neumannCorrectedInverse_lower_bound (R : Y →L[𝕜] X) (P : X →L[𝕜] Y)
    (h : ‖R ∘L P‖ < 1) (C H : ℝ) (hR : ‖R‖ ≤ C) (hq : C * ‖P‖ ≤ 1 / 2)
    (J : X →L[𝕜] Z) (hJ : ‖J ∘L R‖ ≤ H) (f : Y) :
    ‖J (neumannCorrectedInverse R P h f)‖ ≤ 2 * H * ‖f‖ := by
  have hH := (norm_nonneg (J ∘L R)).trans hJ
  let u := neumannCorrectedInverse R P h f
  have hu := neumannCorrectedInverse_bound R P h C hR hq f
  have hpu : ‖P u‖ ≤ ‖f‖ := by
    have h := (P.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg P))
    have hq' := mul_le_mul_of_nonneg_right hq (norm_nonneg f)
    nlinarith
  calc
    ‖J u‖ = ‖(J ∘L R) (f + P u)‖ := by
      congr 1
      exact congrArg J (neumannCorrectedInverse_fixed R P h f)
    _ ≤ ‖J ∘L R‖ * ‖f + P u‖ := (J ∘L R).le_opNorm _
    _ ≤ H * (‖f‖ + ‖P u‖) := mul_le_mul hJ (norm_add_le _ _) (norm_nonneg _) hH
    _ ≤ H * (‖f‖ + ‖f‖) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hpu) hH
    _ = _ := by ring
end Neumann

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma rescaledCoefficient_sobolev_tendsto (f χ : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) (s : ℝ) :
    Filter.Tendsto (fun r => schwartzToSobolev s (rescaledCoefficient f χ hf hχ hχc p r))
      (𝓝 0) (𝓝 0) := by
  simpa only [map_zero, Function.comp_def] using! (schwartzToSobolev s).continuous.continuousAt.tendsto.comp
    (rescaledCoefficient_tendsto f χ hf hχ hχc p)

lemma rescaledCoefficient_sobolev_small (f χ : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) (s ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r in 𝓝 (0 : ℝ), ‖schwartzToSobolev s (rescaledCoefficient f χ hf hχ hχc p r)‖ < ε := by
  have h := (rescaledCoefficient_sobolev_tendsto f χ hf hχ hχc p s).norm
  simpa only [norm_zero] using h.eventually (gt_mem_nhds (by simpa only [norm_zero] using hε))

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

lemma anisotropic_composition_small (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant L * ‖P‖ ≤ 1 / 2) :
    ‖anisotropicSobolevResolvent L s α hα ∘L P‖ < 1 := by
  apply lt_of_le_of_lt ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right (norm_anisotropicSobolevResolvent_le L s α hα)
      (norm_nonneg P)).trans hP))
  norm_num

def localEllipticInverse (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant L * ‖P‖ ≤ 1 / 2) :
    FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s + 2) :=
  neumannCorrectedInverse (anisotropicSobolevResolvent L s α hα) P
    (anisotropic_composition_small L s α hα P hP)

lemma localEllipticInverse_equation (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant L * ‖P‖ ≤ 1 / 2) (f : FourierSobolevSpace E ℂ s) :
    fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (α + ‖L x‖ ^ 2))
      (fourierSobolevDistribution E ℂ (s + 2) (localEllipticInverse L s α hα P hP f)) -
      fourierSobolevDistribution E ℂ s (P (localEllipticInverse L s α hα P hP f)) =
      fourierSobolevDistribution E ℂ s f := by
  have he : localEllipticInverse L s α hα P hP f =
      anisotropicSobolevResolvent L s α hα (f + P (localEllipticInverse L s α hα P hP f)) :=
    neumannCorrectedInverse_fixed (𝕜 := ℂ)
      (X := FourierSobolevSpace E ℂ (s + 2)) (Y := FourierSobolevSpace E ℂ s)
      (anisotropicSobolevResolvent L s α hα) P (anisotropic_composition_small L s α hα P hP) f
  conv_lhs => lhs; arg 2; rw [he]
  rw [anisotropicSobolevResolvent_equation, map_add, add_sub_cancel_right]

lemma norm_localEllipticInverse_le (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant L * ‖P‖ ≤ 1 / 2) :
    ‖localEllipticInverse L s α hα P hP‖ ≤ 2 * anisotropicConstant L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have : 0 ≤ anisotropicConstant L := le_trans zero_le_one (le_max_left _ _)
    positivity)
  intro f
  exact neumannCorrectedInverse_bound _ _ _ _ (norm_anisotropicSobolevResolvent_le L s α hα) hP f

lemma localEllipticInverse_half_bound (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant L * ‖P‖ ≤ 1 / 2) (f : FourierSobolevSpace E ℂ s) :
    ‖sobolevInclusion (s + 2) (s + 1) (by linarith) (localEllipticInverse L s α hα P hP f)‖ ≤
      2 * (anisotropicConstant L * (Real.sqrt α)⁻¹) * ‖f‖ := by
  apply neumannCorrectedInverse_lower_bound _ _ _ _ _
    (norm_anisotropicSobolevResolvent_le L s α hα) hP
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have : 0 ≤ anisotropicConstant L := le_trans zero_le_one (le_max_left _ _)
    positivity)
  intro u
  exact anisotropicSobolevResolvent_half_bound L s α hα u

lemma eventually_localEllipticInverse_small (L : E ≃L[ℝ] G) (s : ℝ)
    (P : ℝ → FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : Tendsto P (𝓝 0) (𝓝 0)) :
    ∀ᶠ r in 𝓝 (0 : ℝ), anisotropicConstant L * ‖P r‖ ≤ 1 / 2 := by
  have h : Tendsto (fun r => anisotropicConstant L * ‖P r‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using tendsto_const_nhds.mul hP.norm
  exact (h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).mono
    (fun _ hh => hh.le)


end YauCounterexamples
end

end OAI
