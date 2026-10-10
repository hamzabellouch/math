import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedCommutator

namespace OAI

/-! # The actual propagator's pointwise energy derivative -/

open Set

namespace DefocusingNLS

theorem hasDerivAt_expandingProfile_energy (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (q : C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ s, ‖q s‖ ≤ R)
    (f : FourierL2) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    let S := expandingProfileTrajectory a b k L T ha ha1 hk hL hT m R hR q hq f
    let l := expandingRadiusCurve L T hL
    let s := projIcc 0 T hT t
    HasDerivAt (fun τ => ‖S (projIcc 0 T hT τ)‖ ^ 2)
      (-a * ‖expandingLowEnergy a k (l s).1 (l s).2 (S s)‖ ^ 2 +
        (6 - 2 * a - k) * ‖expandingHighEnergy a k (l s).1 (l s).2 (S s)‖ ^ 2 +
        2 * inner ℝ (S s) (expandingLinearizedPotential a k (l s).1 ha ha1 hk (l s).2 m (q s) (S s))) t := by
  intro S l s
  let r := expandingReactionHistory T hT (expandingProfileReaction a k T ha ha1 hk m l q 0) S
  have hr : Continuous r := continuous_expandingReactionHistory T hT _ S
  have he := hasDerivAt_expandingMildEnergy a b k L T ha hk hL hT S r hr f
    (fun s => expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m R hR q hq f s) t ht
  have hrt : r t = expandingLinearizedPotential a k (l s).1 ha ha1 hk (l s).2 m (q s) (S s) := by
    change (-Complex.I) • _ + (0 : FourierL2) = _
    exact add_zero _
  simpa only [hrt, l, s, expandingRadiusCurve, ContinuousMap.coe_mk] using he

end DefocusingNLS

end OAI
