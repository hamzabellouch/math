import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGreenBranchBounds
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledGreen

namespace OAI

/-! Full scalar kernel bounds imply the coupled perturbation bound, including
the endpoints of both integration intervals. -/

open Set
namespace DefocusingNLS

theorem spectralCoupledGreen_full_small
    (R E r kap A C M : ℝ) (hR : 0 < R) (hr : r ∈ Icc R E)
    (hkap : 0 < kap) (hA : 0 ≤ A) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (kp km : ℝ → ℝ) (hkp : ∀ t ∈ Icc R E, kap ≤ kp t) (hkm : ∀ t ∈ Icc R E, kap ≤ km t)
    (Dp Up Dm Um : ℝ → ℂ × ℂ) (Wp Wm : ℂ) (fp fm : ℝ → ℂ)
    (hDp : ContinuousOn Dp (Icc R E)) (hUp : ContinuousOn Up (Icc R E))
    (hDm : ContinuousOn Dm (Icc R E)) (hUm : ContinuousOn Um (Icc R E))
    (hfp : ContinuousOn fp (Icc R E)) (hfm : ContinuousOn fm (Icc R E))
    (hWp : Wp ≠ 0) (hWm : Wm ≠ 0)
    (hdetp : spectralScalarWronskian (Dp r) (Up r) = Wp)
    (hdetm : spectralScalarWronskian (Dm r) (Um r) = Wm)
    (hgreenp : ∀ t ∈ Icc R E, spectralShellNorm (kp r) (spectralScalarGreenState Dp Up Wp r t) ≤ A/(kp t))
    (hgreenm : ∀ t ∈ Icc R E, spectralShellNorm (km r) (spectralScalarGreenState Dm Um Wm r t) ≤ A/(km t))
    (hfpb : ∀ t ∈ Icc R E, ‖fp t‖ ≤ C/(kap*t^2)*M)
    (hfmb : ∀ t ∈ Icc R E, ‖fm t‖ ≤ C/(kap*t^2)*M) :
    spectralShellPairNorm (kp r) (km r)
      (spectralScalarGreenIntegral R E Dp Up Wp fp r,
        spectralScalarGreenIntegral R E Dm Um Wm fm r) ≤ (A+1)*C*M/(kap^2*R) := by
  obtain ⟨hpL,hpR⟩ := spectralGreen_closed_branch_bounds Dp Up Wp kp R E A kap r
    hr hA hkap hkp hWp hdetp hgreenp
  obtain ⟨hmL,hmR⟩ := spectralGreen_closed_branch_bounds Dm Um Wm km R E A kap r
    hr hA hkap hkm hWm hdetm hgreenm
  exact spectralCoupledGreen_small R E r kap (A+1) C M hR hr hkap (by linarith) hC hM
    kp km (hkp r hr) (hkm r hr) Dp Up Dm Um Wp Wm fp fm hDp hUp hDm hUm hfp hfm
    hpL hpR hmL hmR hfpb hfmb

end DefocusingNLS

end OAI
