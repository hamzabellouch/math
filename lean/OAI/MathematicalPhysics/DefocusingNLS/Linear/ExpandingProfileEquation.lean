import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingModeEquation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfilePropagator

namespace OAI

/-! # The profile propagator solves the actual moving-torus mode equation -/

open Set

namespace DefocusingNLS

/-- The constructed propagator has the prescribed real-linearized potential in every
physical Fourier mode. Time is differentiated at fixed normalized torus position. -/
theorem hasDerivAt_expandingProfileTrajectory_coefficient
    (a b k L T : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (hL : 1 ≤ L) (hT : 0 ≤ T) (m : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (q : C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ t, ‖q t‖ ≤ R)
    (u₀ : FourierL2) (t : ℝ) (ht : t ∈ Ioo 0 T) (n : frequencyLattice) :
    let S := expandingProfileTrajectory a b k L T ha ha1 hk hL hT m R hR q hq u₀
    let t' : Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    HasDerivAt (fun s => expandingFourierCoefficient a k (expandingRadius L s)
        (S (projIcc 0 T hT s)) n)
      (expandingModeRate a b L t n *
          expandingFourierCoefficient a k (expandingRadius L t) (S t') n -
        Complex.I * expandingFourierCoefficient a k (expandingRadius L t)
          (fderiv ℝ (expandingOddPower a k (expandingRadius L t) ha ha1 hk
            (hL.trans (expandingRadius_ge L t hL ht.1.le)) m) (q t') (S t')) n) t := by
  intro S t'
  let F := expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0
  let u : ℝ → FourierL2 := fun s => S (projIcc 0 T hT s)
  let r := expandingReactionHistory T hT F S
  have hr : Continuous r := continuous_expandingReactionHistory T hT F S
  have hu (s : ℝ) (hs : s ∈ Icc 0 T) :
      u s = expandingFreeStep a b k L s ha hk hL hs.1 u₀ +
        expandingDuhamel a b k L ha hk hL s r := by
    change S (projIcc 0 T hT s) = _
    rw [projIcc_of_mem _ hs]
    exact expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m R hR q hq u₀ ⟨s, hs⟩
  have h := hasDerivAt_expandingMild_coefficient a b k L T ha hk hL u r u₀ hr.continuousOn
    hu t ht n
  have hut : u t = S t' := by
    dsimp [u, t']
    rw [projIcc_of_mem _ ⟨ht.1.le, ht.2.le⟩]
  have hrt : r t = -Complex.I •
      fderiv ℝ (expandingOddPower a k (expandingRadius L t) ha ha1 hk
        (hL.trans (expandingRadius_ge L t hL ht.1.le)) m) (q t') (S t') := by
    dsimp [r, expandingReactionHistory]
    rw [projIcc_of_mem _ ⟨ht.1.le, ht.2.le⟩]
    change -Complex.I • (_ : FourierL2) + (0 : FourierL2) = _
    exact add_zero _
  apply h.congr_deriv
  rw [hut, hrt, expandingFourierCoefficient_smul]
  ring

end DefocusingNLS

end OAI
