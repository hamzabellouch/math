import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactDeformation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeDeformationJet

namespace OAI

/-! Compact exterior limits are the genuine free deformation field. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_converging_free_deformation
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (nhds z₀)) (r : ℕ → ℝ) (r₀ : ℝ)
    (hr : Tendsto r atTop (nhds r₀)) (hr₀ : innerBoundaryRadius ≤ r₀)
    (hrmem : ∀ i, innerBoundaryRadius < r i)
    (hX : ∀ i, HasRadialExterior
      (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i))
      (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i)=0) :
    let b := radialShootingB (profileMatchingParameter z₀)
    let w := fun i => radialVelocity (6-2*radialShootingA (s i))
      (fun t => ‖radialMatchedProfile (s i) (z i) t‖)
    Tendsto (fun i => w i (r i)/r i) atTop (nhds (radialFreeVelocity b r₀/r₀)) ∧
    Tendsto (fun i => deriv (w i) (r i)) atTop
      (nhds (deriv (radialFreeVelocity b) r₀)) := by
  intro b w
  have hd := radialMatched_converging_exterior_deformation s hs z z₀ hz r r₀ hr hr₀
    hrmem hX hmatch
  obtain ⟨δ,ρ,hδ,_hδm,_hsmall,_hρ,_hupper,hlower⟩ := radialShooting_free_annulus z₀
  have hn : (radialFreeSlowJet (-Complex.I*(b : ℂ)) (radialShootingM z₀)
      (Real.log r₀)).1 ≠ 0 := norm_pos_iff.mp (hδ.trans (hlower (Real.log r₀)
        (Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hr₀)))
  have he := radialFree_deformation_jet b r₀
    (lt_of_lt_of_le (by linarith [innerBoundaryRadius_bounds.1]) hr₀) (radialShootingM z₀) hn
  have hν : -2*radialShootingQ z₀=2*Complex.I*(b : ℂ) := by
    dsimp [radialShootingQ,b]
    ring
  dsimp only at hd he
  rw [hν] at hd
  constructor
  · convert hd.1 using 1
    exact congrArg nhds he.1
  · convert hd.2 using 1
    exact congrArg nhds he.2

end DefocusingNLS

end OAI
