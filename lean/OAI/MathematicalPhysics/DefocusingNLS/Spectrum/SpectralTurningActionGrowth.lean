import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningForbiddenGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBFluxMargin

namespace OAI

/-! The forbidden action tends to infinity with the turning radius, already
on the segment between the fixed shell and half the turning radius. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_far_momentum_re_lower (h b eta omega gamma r₀ r : ℝ)
    (heta : 0 ≤ eta) (hr₀ : 0 < r₀) (hr : 0 < r) (hrr : r ≤ r₀/2)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀ = 0) :
    r₀/16 ≤ (spectralLiouvilleMomentum (-1) h b eta omega gamma r).re := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega r
  let p := spectralLiouvilleMomentum (-1) h b eta omega gamma r
  have hfar := (spectralTurning_forbidden_far h b eta omega r₀ r heta hr₀ hr hrr hz).1
  have hFp : 0 < -F := by dsimp only [F]; nlinarith [sq_pos_of_pos hr₀]
  have he : spectralWKBSquaredMomentum (-1) F gamma = ((-F : ℝ) : ℂ)+Complex.I*((-gamma : ℝ) : ℂ) := by
    dsimp only [spectralWKBSquaredMomentum]
    push_cast
    ring
  have hre : (2/3 : ℝ)*‖p‖ ≤ p.re := by
    dsimp only [p,spectralLiouvilleMomentum]
    rw [he]
    exact spectralComplexSqrt_re_two_thirds (-F) (-gamma) hFp
  have hsq : ‖p‖^2 = ‖spectralWKBSquaredMomentum (-1) F gamma‖ := spectralComplexSqrt_norm_sq _
  have hnorm : -F ≤ ‖p‖^2 := (neg_le_abs F).trans (by
    rw [hsq]
    exact spectralWKBSquaredMomentum_norm_lower (-1) F gamma (by norm_num))
  have hplower : r₀/8 ≤ ‖p‖ := by nlinarith [norm_nonneg p]
  change r₀/16 ≤ p.re
  linarith

theorem spectralTurning_forbidden_action_lower (h b eta omega gamma r₀ R E : ℝ)
    (heta : 0 ≤ eta) (hr₀ : 0 < r₀) (hR : 0 < R)
    (hRfour : R ≤ r₀/4) (hEhalf : r₀/2 ≤ E) (hEturn : E < r₀)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀ = 0) :
    r₀^2/64 ≤ (∫ t in R..E, spectralLiouvilleMomentum (-1) h b eta omega gamma t).re := by
  let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
  have hRE : R ≤ E := by linarith
  have hRh : R ≤ r₀/2 := by linarith
  have hF (t : ℝ) (ht : t ∈ Icc R E) :
      0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t := by
    have hh := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      (hR.trans_le ht.1) hr₀ (ht.2.trans_lt hEturn)
    rw [hz] at hh
    linarith
  have hpc : ContinuousOn p (Icc R E) := fun t ht =>
    (spectralLiouvilleMomentum_hasDerivAt (-1) h b eta omega gamma t
      (hR.trans_le ht.1) (hF t ht)).continuousAt.continuousWithinAt
  have hrc : ContinuousOn (fun t => (p t).re) (Icc R E) :=
    Complex.continuous_re.comp_continuousOn hpc
  have hi₁ : IntervalIntegrable (fun t => (p t).re) volume R (r₀/2) :=
    (hrc.mono (Icc_subset_Icc le_rfl hEhalf)).intervalIntegrable_of_Icc hRh
  have hi₂ : IntervalIntegrable (fun t => (p t).re) volume (r₀/2) E :=
    (hrc.mono (Icc_subset_Icc hRh le_rfl)).intervalIntegrable_of_Icc hEhalf
  have hlow : (r₀/2-R)*(r₀/16) ≤ ∫ t in R..r₀/2, (p t).re := by
    calc
      _ = ∫ _t in R..r₀/2, r₀/16 := by
        simp only [intervalIntegral.integral_const,smul_eq_mul]
      _ ≤ _ := intervalIntegral.integral_mono_on hRh intervalIntegrable_const hi₁
        (fun t ht => spectralTurning_far_momentum_re_lower h b eta omega gamma r₀ t
          heta hr₀ (hR.trans_le ht.1) ht.2 hz)
  have hpos : 0 ≤ ∫ t in r₀/2..E, (p t).re := intervalIntegral.integral_nonneg hEhalf
    (fun t _ => spectralComplexSqrt_re_nonneg _)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  have hreal : (∫ t in R..E, p t).re = ∫ t in R..E, (p t).re := by
    exact (intervalIntegral.intervalIntegral_re (hpc.intervalIntegrable_of_Icc hRE)).symm
  change r₀^2/64 ≤ (∫ t in R..E, p t).re
  rw [hreal]
  nlinarith

end DefocusingNLS

end OAI
