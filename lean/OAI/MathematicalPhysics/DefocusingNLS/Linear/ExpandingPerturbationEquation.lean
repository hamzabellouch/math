import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPerturbationReaction
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingResidualStability

namespace OAI

/-! # The nonlinear perturbation equation is the actual Schrödinger mild equation

Subtracting a forced profile gives exactly the reaction used in the nonlinear
step estimates.  Conversely, adding that profile to a perturbation solution
reconstructs an unforced nonlinear mild solution.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem expandingPerturbation_add_mild (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T) (m : ℕ)
    (q g v : C(Icc (0 : ℝ) T, FourierL2)) (q₀ v₀ : FourierL2)
    (hq : ∀ t : Icc (0 : ℝ) T, q t =
      expandingFreeStep a b k L t ha hk hL t.2.1 q₀ +
        expandingDuhamel a b k L ha hk hL t (fun τ =>
          expandingReactionHistory T hT
            (expandingNonlinearReaction a k L T ha ha1 hk hL m) q τ +
              g (projIcc 0 T hT τ)))
    (hv : v = expandingPicard a b k L T ha hk hL hT
      (expandingPerturbationReaction a k L T ha ha1 hk hL m q g) v₀ v) :
    q + v = expandingPicard a b k L T ha hk hL hT
      (expandingNonlinearReaction a k L T ha ha1 hk hL m) (q₀ + v₀) (q + v) := by
  let N := expandingNonlinearReaction a k L T ha ha1 hk hL m
  let P := expandingPerturbationReaction a k L T ha ha1 hk hL m q g
  let r := fun τ => expandingReactionHistory T hT N q τ + g (projIcc 0 T hT τ)
  let f := expandingReactionHistory T hT P v
  have hr : Continuous r := (continuous_expandingReactionHistory T hT N q).add
    (g.continuous.comp continuous_projIcc)
  have hf : Continuous f := continuous_expandingReactionHistory T hT P v
  have he : expandingReactionHistory T hT N (q + v) = fun τ => r τ + f τ := by
    funext τ
    let s := projIcc 0 T hT τ
    let H : FourierL2 → FourierL2 := expandingOddPower a k
      (expandingRadiusCurve L T hL s).1 ha ha1 hk (expandingRadiusCurve L T hL s).2 m
    change (-Complex.I) • H (q s + v s) = ((-Complex.I) • H (q s) + g s) +
      ((-Complex.I) • (H (q s + v s) - H (q s)) - g s)
    simp only [smul_sub]
    abel
  apply ContinuousMap.ext
  intro t
  have hv' := congrArg (fun w : C(Icc (0 : ℝ) T, FourierL2) => w t) hv
  change v t = expandingFreeStep a b k L t ha hk hL t.2.1 v₀ +
    expandingDuhamel a b k L ha hk hL t f at hv'
  change q t + v t = expandingFreeStep a b k L t ha hk hL t.2.1 (q₀ + v₀) +
    expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT N (q + v))
  rw [hq t, hv', map_add, he, expandingDuhamel_add a b k L ha hk hL t r f
    hr.continuousOn hf.continuousOn]
  abel

theorem expandingPerturbation_sub_mild (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T) (m : ℕ)
    (q g u : C(Icc (0 : ℝ) T, FourierL2)) (q₀ u₀ : FourierL2)
    (hq : ∀ t : Icc (0 : ℝ) T, q t =
      expandingFreeStep a b k L t ha hk hL t.2.1 q₀ +
        expandingDuhamel a b k L ha hk hL t (fun τ =>
          expandingReactionHistory T hT
            (expandingNonlinearReaction a k L T ha ha1 hk hL m) q τ +
              g (projIcc 0 T hT τ)))
    (hu : u = expandingPicard a b k L T ha hk hL hT
      (expandingNonlinearReaction a k L T ha ha1 hk hL m) u₀ u) :
    u - q = expandingPicard a b k L T ha hk hL hT
      (expandingPerturbationReaction a k L T ha ha1 hk hL m q g) (u₀ - q₀) (u - q) := by
  let N := expandingNonlinearReaction a k L T ha ha1 hk hL m
  let P := expandingPerturbationReaction a k L T ha ha1 hk hL m q g
  let r := fun τ => expandingReactionHistory T hT N q τ + g (projIcc 0 T hT τ)
  let f := expandingReactionHistory T hT N u
  have hr : Continuous r := (continuous_expandingReactionHistory T hT N q).add
    (g.continuous.comp continuous_projIcc)
  have hf : Continuous f := continuous_expandingReactionHistory T hT N u
  have he : expandingReactionHistory T hT P (u - q) = fun τ => f τ - r τ := by
    funext τ
    let s := projIcc 0 T hT τ
    let H : FourierL2 → FourierL2 := expandingOddPower a k
      (expandingRadiusCurve L T hL s).1 ha ha1 hk (expandingRadiusCurve L T hL s).2 m
    change (-Complex.I) • (H (q s + (u s - q s)) - H (q s)) - g s =
      (-Complex.I) • H (u s) - ((-Complex.I) • H (q s) + g s)
    rw [show q s + (u s - q s) = u s by abel, smul_sub]
    abel
  apply ContinuousMap.ext
  intro t
  have hu' := congrArg (fun w : C(Icc (0 : ℝ) T, FourierL2) => w t) hu
  change u t = expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
    expandingDuhamel a b k L ha hk hL t f at hu'
  change u t - q t = expandingFreeStep a b k L t ha hk hL t.2.1 (u₀ - q₀) +
    expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT P (u - q))
  rw [hu', hq t, map_sub, he, expandingDuhamel_sub a b k L ha hk hL t f r
    hf.continuousOn hr.continuousOn]
  abel

end DefocusingNLS

end OAI
