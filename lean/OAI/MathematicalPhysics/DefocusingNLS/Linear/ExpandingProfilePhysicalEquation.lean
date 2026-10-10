import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfilePointwise
import OAI.MathematicalPhysics.DefocusingNLS.Profile.MovingSobolevEquation

namespace OAI

/-! # The actual profile propagator at fixed physical positions -/

open Set

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] expandingProfileTrajectory expandingTorusFunction

theorem hasDerivAt_expandingProfile_physical (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (q : C(Icc (0 : ℝ) T, FourierL2))
    (hq : ∀ s, ‖q s‖ ≤ Q) (f : FourierL2) (t : ℝ) (ht : t ∈ Ioo 0 T) (y : E) :
    let S := expandingProfileTrajectory a b k L T ha ha1 hk hL hT m Q hQ q hq f
    let W := fun s => expandingToSobolev a k ha1 hk
      (expandingPhysicalPath a k L T ha hk hL S (projIcc 0 T hT s))
    let Z := fun s => expandingToSobolev a k ha1 hk
      (expandingPhysicalPath a k L T ha hk hL q (projIcc 0 T hT s))
    let x := fun s => euclideanToTorus ((expandingRadius L s)⁻¹ • y)
    HasDerivAt (fun s => sobolevTorusFunction k (W s) (x s))
      (((-(a : ℂ) + Complex.I * b) * sobolevTorusFunction k (W t) (x t) +
        ((L ^ (-2 : ℝ) * Real.exp (-t) : ℝ) : ℂ) *
          (Complex.I * torusFourierLaplacian k (W t) (x t)) -
        Complex.I * oddPowerDerivative m (sobolevTorusFunction k (Z t) (x t))
          (sobolevTorusFunction k (W t) (x t))) +
        (-((expandingRadius L t)⁻¹) / 2) •
          sobolevPhysicalDirectional k (W t) ((expandingRadius L t)⁻¹ • y) y) t := by
  intro S W Z x
  let r := expandingReactionHistory T hT
    (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0) S
  have hr : Continuous r := continuous_expandingReactionHistory T hT _ S
  have hs := hasDerivAt_expandingMild_strong a b k L T ha hk hL hT S r hr f
    (fun s => expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m Q hQ q hq f s) t ht
  have h := hasDerivAt_expandingToSobolev_reduced a b k L ha1 hk _ _ t hs
  exact hasDerivAt_sobolev_moving_point k L hk W t y _ _ h
    (hasDerivAt_expandingProfile_pointwise a b k L T ha ha1 hk hL hT m Q hQ q hq f t ht (x t))

end DefocusingNLS

end OAI
