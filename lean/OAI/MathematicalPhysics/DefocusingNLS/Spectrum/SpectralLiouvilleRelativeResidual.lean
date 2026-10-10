import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidualContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBWeightedPrimitives
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningDerivativeBounds

namespace OAI

/-! Integrate the residual using the exact derivative of the reciprocal
real momentum and a relative bound for the frequency slope. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_relative_residual (p g e K L : ℝ) (hp : 0 < p) (hg : 0 ≤ g)
    (_hK : 0 ≤ K) (_hL : 0 ≤ L) (hgp : g ≤ K*p^2) (he : |e| ≤ L*g) :
    (5/16 : ℝ)*g^2/p^5+|e|/(4*p^3) ≤ ((5/16)*K+L/4)*(g/p^3) := by
  have hsq : g^2 ≤ K*p^2*g := by nlinarith [mul_le_mul_of_nonneg_right hgp hg]
  calc
    _ ≤ (5/16 : ℝ)*(K*p^2*g)/p^5+(L*g)/(4*p^3) := by
      exact add_le_add
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity))
        (div_le_div_of_nonneg_right he (by positivity))
    _ = _ := by field_simp

theorem spectralLiouville_relative_residual_integral
    (h b eta omega gamma R E K : ℝ) (hR : 0 < R) (hRE : R ≤ E)
    (heta : 0 ≤ eta) (hK : 0 ≤ K)
    (hF : ∀ t ∈ Icc R E, 0 < homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hg : ∀ t ∈ Icc R E, spectralLiouvilleSlope eta t ≤
      K*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    (∫ t in R..E, ‖spectralLiouvilleResidual 1 h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖) ≤
        2*((5/16)*K+3/(4*R))/Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega R) := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega
  let p := fun t => Real.sqrt (F t)
  let g := spectralLiouvilleSlope eta
  let B := (5/16 : ℝ)*K+3/(4*R)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hFD (t : ℝ) (ht : t ∈ Icc R E) : HasDerivAt F (g t) t :=
    homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t (hR.trans_le ht.1)
  have hFc : ContinuousOn F (Icc R E) := fun t ht => (hFD t ht).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Icc R E) := Real.continuous_sqrt.comp_continuousOn hFc
  have hgc : ContinuousOn g (Icc R E) := fun t ht =>
    (spectralLiouvilleSlope_hasDerivAt eta t (hR.trans_le ht.1)).continuousAt.continuousWithinAt
  have hp (t : ℝ) (ht : t ∈ Icc R E) : 0 < p t := Real.sqrt_pos.mpr (hF t ht)
  have hg0 (t : ℝ) (ht : t ∈ Icc R E) : 0 ≤ g t := by
    dsimp only [g,spectralLiouvilleSlope]
    have ht0 := hR.trans_le ht.1
    positivity
  have hps (t : ℝ) (ht : t ∈ Icc R E) : (p t)^2 = F t := Real.sq_sqrt (hF t ht).le
  have hbound (t : ℝ) (ht : t ∈ Icc R E) :
      ‖spectralLiouvilleResidual 1 h b eta omega gamma t‖/
        ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖ ≤ B*(g t/(p t)^3) := by
    have he := spectralLiouville_weighted_residual_le 1 h b eta omega gamma t (by norm_num) (hF t ht).ne'
    rw [abs_of_pos (hF t ht)] at he
    apply he.trans
    rw [show B = (5/16 : ℝ)*K+(3/R)/4 by dsimp only [B]; ring]
    apply spectralWKB_relative_residual (p t) (g t) (spectralLiouvilleSecond eta t) K (3/R) (hp t ht) (hg0 t ht) hK (by positivity)
    · simpa only [hps t ht] using hg t ht
    · exact (spectralLiouvilleSecond_relative eta t heta (hR.trans_le ht.1)).trans
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) hR ht.1) (hg0 t ht))
  have hi : IntervalIntegrable (fun t => g t/(p t)^3) volume R E :=
    (hgc.div (hpc.pow 3) (fun t ht => pow_ne_zero _ (hp t ht).ne')).intervalIntegrable_of_Icc hRE
  have hf := (spectralLiouvilleResidual_continuousOn 1 h b eta omega gamma R E
    (by norm_num) hR (by simpa only [one_mul] using hF)).2
  have hcomp := intervalIntegral.integral_mono_on hRE (hf.intervalIntegrable_of_Icc hRE)
    (hi.const_mul B) hbound
  rw [intervalIntegral.integral_const_mul] at hcomp
  have hInt := spectralWKB_integral_cube R E hRE p g hpc hgc hp
    (fun t ht => (hFD t ⟨ht.1.le,ht.2.le⟩).sqrt (hF t ⟨ht.1.le,ht.2.le⟩).ne')
  rw [hInt] at hcomp
  calc
    _ ≤ B*(2/p R-2/p E) := hcomp
    _ ≤ B*(2/p R) := mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) hB
    _ = _ := by dsimp only [B,p,F]; ring

end DefocusingNLS

end OAI
