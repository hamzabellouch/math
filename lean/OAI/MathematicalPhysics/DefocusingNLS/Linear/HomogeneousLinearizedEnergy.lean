import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMildEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedFlow

namespace OAI

/-! # Energy balance for the actual linearized propagator

The continuous potential history used to construct the finite-slab flow
gives exactly the energy pairing with the true odd-power derivative.
This specialization retains the manuscript's two homogeneous energies.
-/

open MeasureTheory Set

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

theorem homogeneousLinearizedTrajectory_energy_balance
    (a b k T : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (q f : HomogeneousY a k) (t : Icc (0 : ℝ) T) :
    let S := homogeneousLinearizedTrajectory a b k T ha ha1 hk hT m q f
    let B := homogeneousLinearizedPotential a k ha ha1 hk m q
    ‖S t‖ ^ 2 = ‖f‖ ^ 2 + ∫ τ in (0 : ℝ)..(t : ℝ),
      -a * ‖homogeneousLowEnergy a k ha1 hk (S (projIcc 0 T hT τ))‖ ^ 2 +
      (6 - 2 * a - k) * ‖homogeneousHighEnergy a k ha1 hk (S (projIcc 0 T hT τ))‖ ^ 2 +
      2 * inner ℝ (S (projIcc 0 T hT τ)) (B (S (projIcc 0 T hT τ))) := by
  dsimp only
  let S := homogeneousLinearizedTrajectory a b k T ha ha1 hk hT m q f
  let B := homogeneousLinearizedPotential a k ha ha1 hk m q
  let r := homogeneousPotentialHistory T hT B S
  let u := homogeneousForcedTrajectory a b k ha ha1 hk f r
  have hr : Continuous r := continuous_homogeneousPotentialHistory T hT B S
  have hu (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) : u τ = S (projIcc 0 T hT τ) := by
    change homogeneousFreeOperator a b k τ ha ha1 hk f +
      homogeneousDuhamel a b k ha ha1 hk τ r = S (projIcc 0 T hT τ)
    have hp : projIcc 0 T hT τ = ⟨τ, hτ⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val (projIcc_of_mem hT hτ)
    rw [hp]
    exact (homogeneousLinearizedTrajectory_eq a b k T ha ha1 hk hT m q f ⟨τ, hτ⟩).symm
  have ht : u (t : ℝ) = S t := by
    rw [hu t t.2]
    congr 1
    apply Subtype.ext
    exact congrArg Subtype.val (projIcc_of_mem hT t.2)
  have he := homogeneousForcedEnergy_balance a b k ha ha1 hk f r hr t
  change ‖u (t : ℝ)‖ ^ 2 = _ at he
  rw [ht] at he
  change ‖S t‖ ^ 2 = _
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro τ hτ
  have hτ' : τ ∈ Icc (0 : ℝ) T := by
    rw [uIcc_of_le t.2.1] at hτ
    exact ⟨hτ.1, hτ.2.trans t.2.2⟩
  dsimp only [u] at hu
  dsimp only
  rw [hu τ hτ']
  rfl

end DefocusingNLS

end OAI
