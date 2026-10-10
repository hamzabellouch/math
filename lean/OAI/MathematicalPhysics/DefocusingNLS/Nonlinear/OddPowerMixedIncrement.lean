import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.OddPowerNonlinearity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Mixed increments of the scalar odd-power nonlinearity

The extra factor of the increment preserves the decaying tail weight when
the background profile varies at a fixed power.
-/

open Set Metric

namespace DefocusingNLS

theorem exists_oddPower_derivative_lipschitz (m : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z w : ℂ, ‖z‖ ≤ R → ‖w‖ ≤ R →
      ‖fderiv ℝ (oddPowerNonlinearity m) z -
        fderiv ℝ (oddPowerNonlinearity m) w‖ ≤ C * ‖z - w‖ := by
  have hN := contDiff_oddPowerNonlinearity m
  have hD := (contDiff_infty_iff_fderiv.mp (hN.of_le (by simp))).2
  have hDD : Continuous (fderiv ℝ (fderiv ℝ (oddPowerNonlinearity m))) :=
    (contDiff_infty_iff_fderiv.mp hD).2.continuous
  have hnorm : Continuous (fun x : ℂ => ‖fderiv ℝ (fderiv ℝ (oddPowerNonlinearity m)) x‖) := by
    let V := ℂ →L[ℝ] ℂ →L[ℝ] ℂ
    let G : SeminormedAddGroup V := inferInstance
    have hd : @Continuous ℂ V inferInstance G.toUniformSpace.toTopologicalSpace
        (fderiv ℝ (fderiv ℝ (oddPowerNonlinearity m))) := by
      convert! hDD using 1
    have hn := (@continuous_norm V G).comp hd
    convert! hn using 1
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hnorm.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z w hz hw
  apply (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hD.differentiable (by simp) x)
  · intro x hx
    have hcx : ‖fderiv ℝ (fderiv ℝ (oddPowerNonlinearity m)) x‖ ≤ C := by
      apply (Real.le_norm_self _).trans
      convert! hC x hx using 1
    exact hcx.trans (le_max_left _ _)
  · simpa using hw
  · simpa using hz

/-- For fixed power and a fixed bounded ball, varying the background changes
the nonlinear increment by at most `C * ‖f-g‖ * ‖h‖`. -/
theorem exists_oddPower_mixed_increment_bound (m : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g h : ℂ, ‖f‖ ≤ M → ‖g‖ ≤ M → ‖h‖ ≤ M →
      ‖(oddPowerNonlinearity m (f + h) - oddPowerNonlinearity m f) -
        (oddPowerNonlinearity m (g + h) - oddPowerNonlinearity m g)‖ ≤
        C * ‖f - g‖ * ‖h‖ := by
  obtain ⟨C, hC, hb⟩ := exists_oddPower_derivative_lipschitz m (2 * M)
  refine ⟨C, hC, ?_⟩
  intro f g h hf hg hh
  let F : ℂ → ℂ := fun x => oddPowerNonlinearity m (x + h) - oddPowerNonlinearity m x
  have hF (x : ℂ) : HasFDerivAt F
      (fderiv ℝ (oddPowerNonlinearity m) (x + h) -
        fderiv ℝ (oddPowerNonlinearity m) x) x := by
    have hshift : HasFDerivAt (fun y : ℂ => y + h) (ContinuousLinearMap.id ℝ ℂ) x :=
      (hasFDerivAt_id x).add_const h
    have hN := (contDiff_oddPowerNonlinearity m).differentiable (by simp)
    convert! ((hN (x + h)).hasFDerivAt.comp x hshift).sub (hN x).hasFDerivAt using 1
  have hdb : ∀ x ∈ closedBall (0 : ℂ) M,
      ‖fderiv ℝ (oddPowerNonlinearity m) (x + h) -
        fderiv ℝ (oddPowerNonlinearity m) x‖ ≤ C * ‖h‖ := by
    intro x hx
    have hxM : ‖x‖ ≤ M := by simpa using hx
    have hx2 : ‖x‖ ≤ 2 * M := by linarith
    have hxh : ‖x + h‖ ≤ 2 * M := (norm_add_le x h).trans (by linarith)
    simpa only [add_sub_cancel_left] using hb (x + h) x hxh hx2
  have hbound := (convex_closedBall (0 : ℂ) M).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hF x).hasFDerivWithinAt) hdb
    (show g ∈ closedBall (0 : ℂ) M by simpa using hg)
    (show f ∈ closedBall (0 : ℂ) M by simpa using hf)
  change ‖F f - F g‖ ≤ _
  exact hbound.trans_eq (by ring)

end DefocusingNLS

end OAI
