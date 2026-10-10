import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGaugeEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLogGaugeCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedMultiplierLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMassDivergence

namespace OAI

/-! The coefficients of the actual gauge equation are precisely those of the weak pencil. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedGauge_coefficients (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    let Q := radialMatchedEvenProfile n z
    let μ := radialMatchedMassFunction n z
    let A := radialMatchedTransportFunction n z
    HasDerivAt μ (2*(star (Q r)*deriv Q r).re) r ∧
    HasDerivAt A ((6-2*radialShootingA n)*μ r-11/r*A r) r ∧
    (deriv Q r/Q r+star (deriv Q r)/star (Q r)=
      ((2*(star (Q r)*deriv Q r).re : ℝ) : ℂ)/(μ r : ℂ)) ∧
    ((r : ℂ)/2-Complex.I*(deriv Q r/Q r-star (deriv Q r)/star (Q r))=
      (A r : ℂ)/(μ r : ℂ)) := by
  dsimp only
  have he := radialMatchedEvenProfile_eventuallyEq n z r hr
  have hμ : HasDerivAt (radialMatchedMassFunction n z)
      (2*(star (radialMatchedProfile n z r)*deriv (radialMatchedProfile n z) r).re) r := by
    have h := radialComplexNormSq_hasDerivAt (radialMatchedProfile n z) r
      (radialMatchedProfile_differentiable n z hX hz r)
    apply h.congr_of_eventuallyEq
    exact Eventually.of_forall (fun t => Complex.sq_norm (radialMatchedProfile n z t))
  have hAeq (t : ℝ) (ht : 0 < t) : radialMatchedTransportFunction n z t=
      radialWeightedFlux (radialMatchedProfile n z) t :=
    (radialMatchedWeightedFlux_average_nonneg n z hX hz t ht.le).symm
  have hA := (radialMatchedWeightedFlux_hasDerivAt n z hX hz r hr).congr_of_eventuallyEq
    (show radialMatchedTransportFunction n z =ᶠ[𝓝 r] radialWeightedFlux (radialMatchedProfile n z) from by
      filter_upwards [Ioi_mem_nhds hr] with t ht
      exact hAeq t ht)
  have hm : radialMatchedMassFunction n z r=Complex.normSq (radialMatchedEvenProfile n z r) := by
    rw [he.eq_of_nhds]
    exact Complex.sq_norm _
  have hmn : radialMatchedMassFunction n z r ≠ 0 := by
    rw [hm]
    exact (Complex.normSq_pos.mpr (radialMatchedEvenProfile_ne_zero n z hX r)).ne'
  have hAvalue : radialMatchedTransportFunction n z r=
      r/2*Complex.normSq (radialMatchedEvenProfile n z r)+
        2*(star (radialMatchedEvenProfile n z r)*deriv (radialMatchedEvenProfile n z) r).im := by
    rw [hAeq r hr]
    simp only [radialWeightedFlux,he.eq_of_nhds,he.deriv_eq]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [he.eq_of_nhds,he.deriv_eq] using hμ
  · simpa only [← hAeq r hr,radialMatchedMassFunction,Complex.sq_norm] using hA
  · rw [spectralLogGauge_mass,← hm]
    push_cast
    rfl
  · rw [spectralLogGauge_transport,hAvalue,← hm]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hmn]

end DefocusingNLS

end OAI
