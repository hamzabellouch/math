import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGreenSmallness

namespace OAI

/-! The two scalar Green estimates combine in the maximum channel norm. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralCoupledGreen_small
    (R E r kap A C M : ℝ) (hR : 0<R) (hr : r ∈ Icc R E)
    (hkap : 0<kap) (hA : 0≤ A) (hC : 0≤ C) (hM : 0≤ M)
    (kp km : ℝ → ℝ) (hkp : kap≤ kp r) (hkm : kap≤ km r)
    (Dp Up Dm Um : ℝ → ℂ × ℂ) (Wp Wm : ℂ) (fp fm : ℝ → ℂ)
    (hDp : ContinuousOn Dp (Icc R E)) (hUp : ContinuousOn Up (Icc R E))
    (hDm : ContinuousOn Dm (Icc R E)) (hUm : ContinuousOn Um (Icc R E))
    (hfp : ContinuousOn fp (Icc R E)) (hfm : ContinuousOn fm (Icc R E))
    (hpL : ∀ t ∈ Icc R r, spectralShellNorm (kp r) (((Dp t).1/Wp) • Up r)≤ A/kap)
    (hpR : ∀ t ∈ Icc r E, spectralShellNorm (kp r) (((Up t).1/Wp) • Dp r)≤ A/kap)
    (hmL : ∀ t ∈ Icc R r, spectralShellNorm (km r) (((Dm t).1/Wm) • Um r)≤ A/kap)
    (hmR : ∀ t ∈ Icc r E, spectralShellNorm (km r) (((Um t).1/Wm) • Dm r)≤ A/kap)
    (hfpb : ∀ t ∈ Icc R E, ‖fp t‖≤ C/(kap*t^2)*M)
    (hfmb : ∀ t ∈ Icc R E, ‖fm t‖≤ C/(kap*t^2)*M) :
    spectralShellPairNorm (kp r) (km r)
      (spectralScalarGreenIntegral R E Dp Up Wp fp r,
        spectralScalarGreenIntegral R E Dm Um Wm fm r)≤ A*C*M/(kap^2*R) := by
  apply max_le
  · exact spectralScalarGreenIntegral_small R E r (kp r) kap A C M hR hr
      (hkap.le.trans hkp) hkap hA hC hM Dp Up Wp fp hDp hUp hfp hpL hpR hfpb
  · exact spectralScalarGreenIntegral_small R E r (km r) kap A C M hR hr
      (hkap.le.trans hkm) hkap hA hC hM Dm Um Wm fm hDm hUm hfm hmL hmR hfmb

end DefocusingNLS

end OAI
