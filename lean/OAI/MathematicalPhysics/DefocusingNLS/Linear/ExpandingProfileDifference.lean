import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonlinearStepError
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLocalDependence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPerturbationExistence

namespace OAI

/-! # Differences in the actual profile-linearized evolution

Subtracting two forced linearized trajectories preserves the linearized
equation, with the difference of their initial data and forcing.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem expandingProfileTrajectory_sub (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R) (q : C(Icc (0 : ℝ) T, FourierL2))
    (hq : ∀ t, ‖q t‖ ≤ R) (u₀ v₀ : FourierL2) :
    expandingProfileTrajectory a b k L T ha ha1 hk hL hT m R hR q hq (u₀ - v₀) =
      expandingProfileTrajectory a b k L T ha ha1 hk hL hT m R hR q hq u₀ -
        expandingProfileTrajectory a b k L T ha ha1 hk hL hT m R hR q hq v₀ := by
  have hn : expandingProfileTrajectory a b k L T ha ha1 hk hL hT m R hR q hq (-v₀) =
      -expandingProfileTrajectory a b k L T ha ha1 hk hL hT m R hR q hq v₀ := by
    simpa only [neg_one_smul] using
      expandingProfileTrajectory_smul a b k L T ha ha1 hk hL hT m R hR q hq (-1) v₀
  simpa only [sub_eq_add_neg, hn] using
    expandingProfileTrajectory_add a b k L T ha ha1 hk hL hT m R hR q hq u₀ (-v₀)

theorem expandingProfile_mild_sub (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T) (m : ℕ)
    (q g h u v : C(Icc (0 : ℝ) T, FourierL2)) (u₀ v₀ : FourierL2)
    (hu : ∀ t : Icc (0 : ℝ) T, u t =
      expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL t
          (expandingReactionHistory T hT
            (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q g) u))
    (hv : ∀ t : Icc (0 : ℝ) T, v t =
      expandingFreeStep a b k L t ha hk hL t.2.1 v₀ +
        expandingDuhamel a b k L ha hk hL t
          (expandingReactionHistory T hT
            (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q h) v)) :
    ∀ t : Icc (0 : ℝ) T, (u - v) t =
      expandingFreeStep a b k L t ha hk hL t.2.1 (u₀ - v₀) +
        expandingDuhamel a b k L ha hk hL t
          (expandingReactionHistory T hT
            (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q (g - h))
            (u - v)) := by
  let F := expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q g
  let G := expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q h
  let H := expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q (g - h)
  let r := expandingReactionHistory T hT F u
  let s := expandingReactionHistory T hT G v
  have hr : Continuous r := continuous_expandingReactionHistory T hT F u
  have hs : Continuous s := continuous_expandingReactionHistory T hT G v
  have he : expandingReactionHistory T hT H (u - v) = fun τ => r τ - s τ := by
    funext τ
    let t := projIcc 0 T hT τ
    let D : FourierL2 →L[ℝ] FourierL2 :=
      fderiv ℝ (expandingOddPower a k (expandingRadiusCurve L T hL t).1
        ha ha1 hk (expandingRadiusCurve L T hL t).2 m) (q t)
    change (-Complex.I) • D (u t - v t) + (g t - h t) =
      ((-Complex.I) • D (u t) + g t) - ((-Complex.I) • D (v t) + h t)
    rw [map_sub, smul_sub]
    abel
  intro t
  change u t - v t = expandingFreeStep a b k L t ha hk hL t.2.1 (u₀ - v₀) +
    expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT H (u - v))
  rw [hu t, hv t, he, expandingDuhamel_sub a b k L ha hk hL t r s
    hr.continuousOn hs.continuousOn, map_sub]
  abel

/-- The nonlinear difference is a forced trajectory of the actual profile
linearization; the common profile defect cancels from its source. -/
theorem expandingPerturbation_difference_linear_mild (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T) (m : ℕ)
    (q g u v : C(Icc (0 : ℝ) T, FourierL2)) (u₀ v₀ : FourierL2)
    (hu : u = expandingPicard a b k L T ha hk hL hT
      (expandingPerturbationReaction a k L T ha ha1 hk hL m q g) u₀ u)
    (hv : v = expandingPicard a b k L T ha hk hL hT
      (expandingPerturbationReaction a k L T ha ha1 hk hL m q g) v₀ v) :
    ∀ t : Icc (0 : ℝ) T, (u - v) t =
      expandingFreeStep a b k L t ha hk hL t.2.1 (u₀ - v₀) +
        expandingDuhamel a b k L ha hk hL t
          (expandingReactionHistory T hT
            (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q
              (expandingPerturbationSource a k L T ha ha1 hk hL m q g u -
                expandingPerturbationSource a k L T ha ha1 hk hL m q g v)) (u - v)) :=
  expandingProfile_mild_sub a b k L T ha ha1 hk hL hT m q
    (expandingPerturbationSource a k L T ha ha1 hk hL m q g u)
    (expandingPerturbationSource a k L T ha ha1 hk hL m q g v) u v u₀ v₀
    (expandingPerturbation_linear_mild a b k L T ha ha1 hk hL hT m q g u u₀ hu)
    (expandingPerturbation_linear_mild a b k L T ha ha1 hk hL hT m q g v v₀ hv)

end DefocusingNLS

end OAI
