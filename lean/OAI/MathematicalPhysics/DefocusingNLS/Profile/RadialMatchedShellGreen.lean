import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledGreen
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellForcingContinuity

namespace OAI

/-! The actual matched profile supplies the small coupled Green correction.
Only the scalar transfer bounds remain as inputs to the fixed-shell estimate. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_shell_green_small (C : ℝ) (hC : 0<C) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z=0) →
      ∀ R E r kap A M : ℝ, innerBoundaryRadius<R → r ∈ Icc R E →
      0<kap → 0≤ A → 0≤ M →
      ∀ kp km : ℝ → ℝ,
      (∀ t ∈ Icc R E, kap≤ kp t) → (∀ t ∈ Icc R E, kap≤ km t) →
      ∀ u : ℝ → (ℂ × ℂ) × (ℂ × ℂ), ContinuousOn u (Icc R E) →
      (∀ t ∈ Icc R E, spectralShellPairNorm (kp t) (km t) (u t)≤ M) →
      ∀ Dp Up Dm Um : ℝ → ℂ × ℂ, ∀ Wp Wm : ℂ,
      ContinuousOn Dp (Icc R E) → ContinuousOn Up (Icc R E) →
      ContinuousOn Dm (Icc R E) → ContinuousOn Um (Icc R E) →
      (∀ t ∈ Icc R r, spectralShellNorm (kp r) (((Dp t).1/Wp) • Up r)≤ A/kap) →
      (∀ t ∈ Icc r E, spectralShellNorm (kp r) (((Up t).1/Wp) • Dp r)≤ A/kap) →
      (∀ t ∈ Icc R r, spectralShellNorm (km r) (((Dm t).1/Wm) • Um r)≤ A/kap) →
      (∀ t ∈ Icc r E, spectralShellNorm (km r) (((Um t).1/Wm) • Dm r)≤ A/kap) →
      spectralShellPairNorm (kp r) (km r)
        (spectralScalarGreenIntegral R E Dp Up Wp
          (fun t => spectralShellPlusForcing (n+radialInnerShootingThreshold)
            (radialMatchedProfile n z t) t (u t)) r,
        spectralScalarGreenIntegral R E Dm Um Wm
          (fun t => spectralShellMinusForcing (n+radialInnerShootingThreshold)
            (radialMatchedProfile n z t) t (u t)) r)≤ A*C*M/(kap^2*R) := by
  filter_upwards [radialMatched_shell_forcing_bound C hC] with n hn
  intro z hX hz R E r kap A M hRb hr hkap hA hM kp km hkp hkm u hu huM
    Dp Up Dm Um Wp Wm hDp hUp hDm hUm hpL hpR hmL hmR
  have hR : 0<R := by linarith [innerBoundaryRadius_bounds.1]
  have hQ : ContinuousOn (radialMatchedProfile n z) (Icc R E) :=
    (radialMatchedProfile_contDiffOn n z hX hz).continuousOn.mono
      (fun t ht => hR.trans_le ht.1)
  have hc := spectralShellForcing_continuousOn (n+radialInnerShootingThreshold) R E hR
    (radialMatchedProfile n z) u hQ hu
  apply spectralCoupledGreen_small R E r kap A C M hR hr hkap hA hC.le hM
    kp km (hkp r hr) (hkm r hr) Dp Up Dm Um Wp Wm _ _
    hDp hUp hDm hUm hc.1 hc.2 hpL hpR hmL hmR
  · intro t ht
    exact (hn z t (kp t) (km t) kap (hRb.trans_le ht.1) hkap (hkp t ht) (hkm t ht) (u t)).1.trans
      (mul_le_mul_of_nonneg_left (huM t ht) (by positivity))
  · intro t ht
    exact (hn z t (kp t) (km t) kap (hRb.trans_le ht.1) hkap (hkp t ht) (hkm t ht) (u t)).2.trans
      (mul_le_mul_of_nonneg_left (huM t ht) (by positivity))

end DefocusingNLS

end OAI
