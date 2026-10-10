import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalValueDet
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalAnalytic
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeValueContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralJointNonzero

namespace OAI

/-! A fixed neighborhood with nonvanishing value matrices and holomorphic actual boundaries. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedCanonical_analytic_neighborhood
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀)) (ell : ℕ)
    (Y Z : ℕ → ℂ → ℝ → E₄)
    (hY : ∀ i, IsCanonicalHolomorphicColumn
      (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
      (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (1,0) (Y i))
    (hZ : ∀ i, IsCanonicalHolomorphicColumn
      (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
      (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (0,1) (Z i))
    (R : ℝ) (hR : innerBoundaryRadius < R)
    (hLR : radialShootingR (profileMatchingParameter z₀) < R)
    (lam₀ : ℂ) (hlam₀ : -(1/32 : ℝ) < lam₀.re)
    (hd : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam₀ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam₀ R)) ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ lam₀ ∈ U ∧
      (∀ w ∈ U, -(1/32 : ℝ) ≤ w.re ∧ spectralValueDet
        (spectralPhysicalValueMap (spectralFreePositivePhysical ell
          (radialShootingB (profileMatchingParameter z₀)) w R))
        (spectralPhysicalValueMap (spectralFreeNegativePhysical ell
          (radialShootingB (profileMatchingParameter z₀)) w R)) ≠ 0) ∧
      ∀ᶠ i in atTop, AnalyticOnNhd ℂ (radialMatchedCanonicalFlux (s i) (z i) R (Y i) (Z i)) U := by
  have hj := radialMatchedCanonicalValueDet_joint_tendsto s hs z z₀ hz ell Y Z hY hZ
    R hR lam₀ hlam₀.le
  let Dn := fun i lam => spectralValueDet
    (spectralPhysicalValueMap (spectralPhysicalPair
      (radialShootingNu (s i+radialInnerShootingThreshold) (z i)-2*lam)
      (star (radialShootingNu (s i+radialInnerShootingThreshold) (z i))-2*lam) (Y i lam) R))
    (spectralPhysicalValueMap (spectralPhysicalPair
      (radialShootingNu (s i+radialInnerShootingThreshold) (z i)-2*lam)
      (star (radialShootingNu (s i+radialInnerShootingThreshold) (z i))-2*lam) (Z i lam) R))
  obtain ⟨A,hA,ha,hactual⟩ := spectral_joint_nonzero_neighborhood Dn lam₀ _ hd hj
  let D := fun w : ℂ => spectralValueDet
        (spectralPhysicalValueMap (spectralFreePositivePhysical ell
          (radialShootingB (profileMatchingParameter z₀)) w R))
        (spectralPhysicalValueMap (spectralFreeNegativePhysical ell
          (radialShootingB (profileMatchingParameter z₀)) w R))
  have hDc : ContinuousAt D lam₀ := radialFreeValueDet_continuousAt ell z₀ R hLR lam₀ hlam₀.le
  have he : {w : ℂ | D w ≠ 0} ∈ 𝓝 lam₀ := hDc.tendsto.eventually (eventually_ne_nhds hd)
  have hh : {w : ℂ | -(1/32 : ℝ) < w.re} ∈ 𝓝 lam₀ :=
    Complex.continuous_re.continuousAt.tendsto.eventually (lt_mem_nhds hlam₀)
  obtain ⟨B,hB,hBo,hb⟩ := mem_nhds_iff.mp (inter_mem he hh)
  refine ⟨A ∩ B,hA.inter hBo,⟨ha,hb⟩,?_,?_⟩
  · intro w hw
    exact ⟨(hB hw.2).2.le,(hB hw.2).1⟩
  · filter_upwards [hactual] with i hi w hw
    exact radialMatchedCanonicalFlux_analyticAt (s i) ell (z i) R
      (innerBoundaryRadius_bounds.1.trans hR.le) (Y i) (Z i) (hY i) (hZ i) w (hi w hw.1)

end DefocusingNLS

end OAI
