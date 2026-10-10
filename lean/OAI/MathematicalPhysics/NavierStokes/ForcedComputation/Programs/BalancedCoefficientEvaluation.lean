import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedEvaluation

namespace OAI

/-! Explicit terminating evaluators for the two viscosity-independent force coefficients. -/

noncomputable section
namespace ForcedComputation.BalancedExpressions
open ShearFlows

def evaluateCoefficient₀ (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (α : List (Fin 4)) (b : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  evaluate I hI α (fun _ => 0) b ε hε

def evaluateCoefficient₁ (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (α : List (Fin 4)) (b : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  evaluate I hI α (fun _ => 1) b (ε/2) (by positivity) -
    evaluate I hI α (fun _ => 0) b (ε/2) (by positivity)

private theorem constantName (r : ℚ) : IsFastRealName (fun _ => r) (r : ℝ) := by
  intro n
  simp only [sub_self, abs_zero]
  unfold errorTolerance
  positivity

theorem evaluateCoefficient₀_spec (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (α : List (Fin 4))
    {y : SpaceTime} {b : ℕ → RationalSpaceTime} (hb : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (BalancedVelocity.force₀ I hI) α y -
      rationalVector (evaluateCoefficient₀ I hI α b ε hε)‖ ≤ (ε : ℝ) := by
  simpa only [BalancedVelocity.force₀, evaluateCoefficient₀, Rat.cast_zero] using
    evaluate_spec I hI α (constantName 0) hb ε hε

theorem evaluateCoefficient₁_spec (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (α : List (Fin 4))
    {y : SpaceTime} {b : ℕ → RationalSpaceTime} (hb : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (BalancedVelocity.force₁ I hI) α y -
      rationalVector (evaluateCoefficient₁ I hI α b ε hε)‖ ≤ (ε : ℝ) := by
  have hf : BalancedVelocity.force₁ I hI = residual 1 (BalancedVelocity.velocity I hI) -
      residual 0 (BalancedVelocity.velocity I hI) := by
    have h := BalancedVelocity.force_affine I hI 1
    rw [one_smul] at h
    funext z
    have hz := congrFun h z
    change residual 1 (BalancedVelocity.velocity I hI) z =
      residual 0 (BalancedVelocity.velocity I hI) z + BalancedVelocity.force₁ I hI z at hz
    exact eq_sub_of_add_eq' hz.symm
  have h₁ := evaluate_spec I hI α (constantName 1) hb (ε/2) (by positivity)
  have h₀ := evaluate_spec I hI α (constantName 0) hb (ε/2) (by positivity)
  simp only [Rat.cast_one] at h₁
  simp only [Rat.cast_zero] at h₀
  rw [hf, mixedDerivative_sub
    (residual_smooth (BalancedVelocity.smooth I hI) 1)
    (residual_smooth (BalancedVelocity.smooth I hI) 0)]
  have hq : rationalVector (evaluateCoefficient₁ I hI α b ε hε) =
      rationalVector (evaluate I hI α (fun _ => 1) b (ε/2) (by positivity)) -
      rationalVector (evaluate I hI α (fun _ => 0) b (ε/2) (by positivity)) := by
    ext j
    exact Rat.cast_sub _ _
  rw [hq]
  simp only [Pi.sub_apply]
  calc
    _ = ‖(mixedDerivative (residual 1 (BalancedVelocity.velocity I hI)) α y -
          rationalVector (evaluate I hI α (fun _ => 1) b (ε/2) (by positivity))) -
        (mixedDerivative (residual 0 (BalancedVelocity.velocity I hI)) α y -
          rationalVector (evaluate I hI α (fun _ => 0) b (ε/2) (by positivity)))‖ := by
      congr 1
      abel
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add h₁ h₀) |>.trans (by
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
      linarith)


end ForcedComputation.BalancedExpressions

end

end OAI
