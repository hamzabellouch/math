import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianDeformation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightComparison
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPressureTransport

namespace OAI

/-! Smooth stationary profiles with uniform coercive geometry and pressure transport. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_coercive_stationary_radialMatchedProfile :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ᶠ n in atTop, ∃ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) ∧
      radialMatchingMap n z=0 ∧
      ContDiff ℝ ∞ (radialMatchedCartesian n z) ∧
      (∀ y : E, stationarySimilarityDefect (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
        (radialMatchedCartesian n z) y=0) ∧
      (∀ y : E, radialMatchedCartesian n z y ≠ 0) ∧
      0 < (radialMatchedCartesian n z 0).re ∧ (radialMatchedCartesian n z 0).im=0 ∧
      (∀ y v : E, c*‖v‖^2 ≤ inner ℝ (fderiv ℝ (radialMatchedVectorField n z) y v) v) ∧
      (∀ r : ℝ, 0 ≤ r →
        d*(1+r^2)^(-2*radialShootingA n) ≤ ‖radialMatchedProfile n z r‖^2 ∧
        ‖radialMatchedProfile n z r‖^2 ≤ 144*(1+r^2)^(-2*radialShootingA n)) ∧
      (∀ r : ℝ, 0 ≤ r →
        ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)) ≤ 1) ∧
      (∀ r : ℝ, 0 ≤ r →
        radialVelocity (6-2*radialShootingA n) (fun t => ‖radialMatchedProfile n z t‖) r*
          deriv (fun t => ‖radialMatchedProfile n z t‖^(2*(n+radialInnerShootingThreshold))/
            radialShootingA n) r ≤ 1600) := by
  obtain ⟨c,hc,hdef⟩ := radialMatchedVectorField_uniform_positive
  obtain ⟨d,hd,hw⟩ := radialMatched_uniform_weight_comparison
  refine ⟨c,d,hc,hd,?_⟩
  filter_upwards [exists_smooth_stationary_radialMatchedProfile,hdef,hw,
    radialMatched_global_pressure_bound,radialMatched_global_pressure_transport_bound]
    with n hn hdn hwn hpn htn
  obtain ⟨z,hX,hz,hQ,hstat,hne,hre,him⟩ := hn
  exact ⟨z,hX,hz,hQ,hstat,hne,hre,him,hdn z hX hz,hwn z,hpn z,htn z hX hz⟩

end DefocusingNLS

end OAI
