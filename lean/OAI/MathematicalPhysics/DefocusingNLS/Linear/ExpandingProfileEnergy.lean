import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMildEnergyBalance
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfilePropagator

namespace OAI

/-! # Exact energy balance for the constructed torus profile propagator

The forcing is the derivative of the actual odd-power nonlinearity at the
given moving profile.  The trajectory is the already constructed unique
finite-slab solution, rather than an assumed energy solution.
-/

open Set MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] expandingProfileTrajectory expandingLowEnergy expandingHighEnergy

theorem expandingProfileTrajectory_energy_balance (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (q : C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ t, ‖q t‖ ≤ R)
    (f : FourierL2) (t : Icc (0 : ℝ) T) :
    let S := expandingProfileTrajectory a b k L T ha ha1 hk hL hT m R hR q hq f
    let l := expandingRadiusCurve L T hL
    ‖S t‖ ^ 2 = ‖f‖ ^ 2 + ∫ τ in (0 : ℝ)..(t : ℝ),
      (let s := projIcc 0 T hT τ;
      -a * ‖expandingLowEnergy a k (l s).1 (l s).2 (S s)‖ ^ 2 +
        (6 - 2 * a - k) * ‖expandingHighEnergy a k (l s).1 (l s).2 (S s)‖ ^ 2 +
        2 * inner ℝ (S s) ((-Complex.I) •
          fderiv ℝ (expandingOddPower a k (l s).1 ha ha1 hk (l s).2 m) (q s) (S s))) := by
  intro S l
  let F := expandingProfileReaction a k T ha ha1 hk m l q 0
  let r := expandingReactionHistory T hT F S
  have hr : Continuous r := continuous_expandingReactionHistory T hT F S
  have hu (s : Icc (0 : ℝ) T) : S s =
      expandingFreeStep a b k L s ha hk hL s.2.1 f +
        expandingDuhamel a b k L ha hk hL s r :=
    expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m R hR q hq f s
  have he := expandingMildEnergy_balance a b k L T ha hk hL hT S r hr f hu t
  have hforce (τ : ℝ) : r τ =
      (-Complex.I) • fderiv ℝ
        (expandingOddPower a k (l (projIcc 0 T hT τ)).1 ha ha1 hk
          (l (projIcc 0 T hT τ)).2 m) (q (projIcc 0 T hT τ)) (S (projIcc 0 T hT τ)) := by
    change (-Complex.I) • _ + (0 : FourierL2) = _
    exact add_zero _
  simp_rw [hforce] at he
  exact he

end DefocusingNLS

end OAI
