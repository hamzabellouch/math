import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalForcingBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellForcingContinuity

namespace OAI

/-! The actual matched profile has uniformly bounded forcing energy on
any terminal subinterval of a fixed shell. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_shell_forcing_energy (R B : ℝ) (hR : innerBoundaryRadius < R)
    (hRB : R ≤ B) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
    HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
    radialMatchingMap n z = 0 →
    ∀ (f g : ℝ → ℂ), ContDiff ℝ 2 f → ContDiff ℝ 2 g →
    ∀ M : ℝ, (∫ r in R..B, spectralPhysicalShellDensity f g r) ≤ M →
    ∀ a ∈ Icc R B,
      (∫ r in a..B, ‖spectralShellMinusForcing (n+radialInnerShootingThreshold)
        (radialMatchedProfile n z r) r (spectralPhysicalLiouvillePair f g r)‖^2) ≤ (1/R^2)^2*M := by
  filter_upwards [homogeneousSpectralLocalization_uniform_potential 1 (by norm_num)] with n hn
  intro z hX hz f g hf hg M hbound a ha
  have hR0 : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  have hqc := spectralPhysicalLiouvillePair_continuous_shell R B hR0 f g hf hg
  have hQc : ContinuousOn (radialMatchedProfile n z) (Icc R B) :=
    (radialMatchedProfile_contDiffOn n z hX hz).continuousOn.mono (fun r hr => hR0.trans_le hr.1)
  have hfc := (spectralShellForcing_continuousOn (n+radialInnerShootingThreshold) R B hR0
    (radialMatchedProfile n z) (spectralPhysicalLiouvillePair f g) hQc hqc).2.norm.pow 2
  have hdc := (spectralPhysicalShellDensity_continuous f g hf hg).continuousOn (s := Icc R B)
  have hb (r : ℝ) (hr : r ∈ Icc R B) :
      ‖spectralShellMinusForcing (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) r
        (spectralPhysicalLiouvillePair f g r)‖^2 ≤ (1/R^2)^2*spectralPhysicalShellDensity f g r := by
    apply spectralPhysicalLiouvillePair_minus_forcing_sq R r hR0 hr.1
    apply (le_div_iff₀ (sq_pos_of_pos (hR0.trans_le hr.1))).mpr
    simpa only [mul_comm] using (hn z r (hR.trans_le hr.1)).le
  have hi := intervalIntegral.integral_mono_on (μ := volume) hRB
    (hfc.intervalIntegrable_of_Icc hRB)
    ((hdc.const_mul ((1/R^2)^2)).intervalIntegrable_of_Icc hRB) hb
  rw [intervalIntegral.integral_const_mul] at hi
  have hfull := hi.trans (mul_le_mul_of_nonneg_left hbound (sq_nonneg _))
  exact (intervalIntegral.integral_mono_interval ha.1 ha.2 le_rfl
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (hfc.intervalIntegrable_of_Icc hRB)).trans hfull

end DefocusingNLS

end OAI
