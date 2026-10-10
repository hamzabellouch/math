import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformTransportBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMassDivergence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformTailDeformation

namespace OAI

/-! The uniformly bounded transport-to-mass ratio is precisely the radial
velocity in the divergence-form spectral identity. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_mass_transport_eq (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 ≤ r) :
    radialMassFlux n z r=r^11*radialMatchedTransportFunction n z r := by
  rw [radialMassFlux_eq n z hX hz r hr]
  congr 1
  exact radialMatchedWeightedFlux_average_nonneg n z hX hz r hr

theorem radialMatched_uniform_velocity_bound (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ r ∈ Icc 0 R,
      |radialMatchedVelocity (s i) (z i) r| ≤ C ∧
      |radialMassFlux (s i) (z i) r| ≤ C*radialMassDensity (s i) (z i) r := by
  obtain ⟨C,hC,hb⟩ := radialMatched_uniform_transport_bound s hs z z₀ hz hX hm R hR
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with i hi r hr
  have hflux : |radialMassFlux (s i) (z i) r| ≤ C*radialMassDensity (s i) (z i) r := by
    rw [radialMatched_mass_transport_eq (s i) (z i) (hX i) (hm i) r hr.1,
      abs_mul,abs_of_nonneg (pow_nonneg hr.1 11)]
    have hh := mul_le_mul_of_nonneg_left (hi r hr).2 (pow_nonneg hr.1 11)
    simpa only [radialMassDensity,radialMatchedMassFunction,mul_assoc,mul_left_comm] using hh
  refine ⟨?_,hflux⟩
  rcases hr.1.eq_or_lt with he | hp
  · subst r
    simpa [radialMatchedVelocity,radialVelocity] using hC
  · have hmass : 0 < radialMassDensity (s i) (z i) r :=
      mul_pos (pow_pos hp 11) (hi r hr).1
    change |radialMassDensity (s i) (z i) r*radialMatchedVelocity (s i) (z i) r| ≤ _ at hflux
    rw [abs_mul,abs_of_pos hmass] at hflux
    exact (mul_le_mul_iff_right₀ hmass).mp (by simpa only [mul_comm] using hflux)

end DefocusingNLS

end OAI
