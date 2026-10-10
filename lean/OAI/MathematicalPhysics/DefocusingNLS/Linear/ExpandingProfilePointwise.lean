import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFixedPhysical
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingReducedTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevForcedEvaluation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfilePropagator

namespace OAI

/-! # The actual profile propagator satisfies the pointwise normalized torus equation -/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingProfileTrajectory expandingTorusFunction

theorem hasDerivAt_expandingProfile_pointwise (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (q : C(Icc (0 : ℝ) T, FourierL2))
    (hq : ∀ s, ‖q s‖ ≤ Q) (f : FourierL2) (t : ℝ) (ht : t ∈ Ioo 0 T)
    (x : SchrodingerTorus) :
    let S := expandingProfileTrajectory a b k L T ha ha1 hk hL hT m Q hQ q hq f
    let W := fun s => expandingToSobolev a k ha1 hk
      (expandingPhysicalPath a k L T ha hk hL S (projIcc 0 T hT s))
    let Z := fun s => expandingToSobolev a k ha1 hk
      (expandingPhysicalPath a k L T ha hk hL q (projIcc 0 T hT s))
    HasDerivAt (fun s => sobolevTorusFunction k (W s) x)
      ((-(a : ℂ) + Complex.I * b) * sobolevTorusFunction k (W t) x +
        ((L ^ (-2 : ℝ) * Real.exp (-t) : ℝ) : ℂ) *
          (Complex.I * torusFourierLaplacian k (W t) x) -
        Complex.I * oddPowerDerivative m (sobolevTorusFunction k (Z t) x)
          (sobolevTorusFunction k (W t) x)) t := by
  intro S W Z
  let r := expandingReactionHistory T hT
    (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0) S
  have hr : Continuous r := continuous_expandingReactionHistory T hT _ S
  let rC : C(Icc (0 : ℝ) T, FourierL2) := ⟨fun s => r s, hr.comp continuous_subtype_val⟩
  let G := fun s => expandingToSobolev a k ha1 hk
    (expandingPhysicalPath a k L T ha hk hL rC (projIcc 0 T hT s))
  have hs := hasDerivAt_expandingMild_strong a b k L T ha hk hL hT S r hr f
    (fun s => expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m Q hQ q hq f s) t ht
  have h := hasDerivAt_expandingToSobolev_reduced a b k L ha1 hk _ _ t hs
  have h' : HasDerivAt (fun s => lowerSobolevInclusion (W s))
      ((-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (W t) +
        ((L ^ (-2 : ℝ) * Real.exp (-t) : ℝ) : ℂ) • lowerSobolevGenerator (W t) +
          lowerSobolevInclusion (G t)) t := by
    apply h.congr_deriv
    change (-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (W t) +
        (L ^ (-2 : ℝ) * Real.exp (-t)) • lowerSobolevGenerator (W t) +
          lowerSobolevInclusion (G t) = _
    apply congrArg (fun v : FourierL2 =>
      (-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (W t) + v + lowerSobolevInclusion (G t))
    ext n
    simp only [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  have hp := hasDerivAt_forcedTorusFunction k hk W t x
    (-(a : ℂ) + Complex.I * b) (((L ^ (-2 : ℝ) * Real.exp (-t) : ℝ) : ℂ)) (G t) h'
  have hg : sobolevTorusFunction k (G t) x = -Complex.I *
      oddPowerDerivative m (sobolevTorusFunction k (Z t) x) (sobolevTorusFunction k (W t) x) := by
    simp only [G, Z, W, expandingFixedPhysical_value a k L T ha ha1 hk hL]
    let s := projIcc 0 T hT t
    have hs' : projIcc 0 T hT (s : ℝ) = s := projIcc_of_mem _ s.2
    change expandingTorusFunction a k (expandingRadius L s) (r s) x = _
    dsimp [r, expandingReactionHistory]
    rw [hs']
    change expandingTorusFunction a k (expandingRadius L s)
      ((-Complex.I) • fderiv ℝ (expandingOddPower a k (expandingRadius L s) ha ha1 hk
        (hL.trans (expandingRadius_ge L s hL s.2.1)) m) (q s) (S s) + 0) x = _
    rw [add_zero, expandingTorusFunction_eq_evaluation a k _ ha ha1 hk
      (hL.trans (expandingRadius_ge L s hL s.2.1)), map_smul]
    simp only [← expandingTorusFunction_eq_evaluation a k _ ha ha1 hk
      (hL.trans (expandingRadius_ge L s hL s.2.1)), smul_eq_mul,
      expandingOddPower_fderiv_pointwise]
    rfl
  convert hp using 1
  rw [hg]
  ring

end DefocusingNLS

end OAI
