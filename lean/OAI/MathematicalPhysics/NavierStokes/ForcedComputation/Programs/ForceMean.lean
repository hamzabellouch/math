import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.AutonomousStartup

namespace OAI

/-!
# The mean of the full startup force

For a periodic incompressible field, the convective acceleration is the
divergence of its momentum flux, and therefore has zero spatial mean. This is
the additional term needed in the autonomous construction; a shear-only force
identity would not suffice.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
open ShearFlows

namespace ForcedComputation

theorem advection_mean_zero {L : ℝ} (hL : 0 ≤ L) {W : Space → Space}
    (hW : ContDiff ℝ ∞ W) (hp : CubePeriodic L W)
    (hd : ∀ x, divergence W x = 0) :
    (∫ x in fundamentalCube L, advection W x) = 0 := by
  have hW₁ : ContDiff ℝ 1 W := hW.of_le (by simp)
  have hi : IntegrableOn (advection W) (fundamentalCube L) :=
    ((hW.continuous_fderiv (by simp)).clm_apply hW.continuous).integrableOn_Icc
  ext j
  change (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ)
    (∫ x in fundamentalCube L, advection W x) = 0
  rw [← (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ).integral_comp_comm hi]
  change (∫ x in fundamentalCube L, advection W x j) = 0
  have hcoord : ContDiff ℝ 1 (fun y => W y j) :=
    (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ).contDiff.comp hW₁
  have he (x : Space) : divergence (fun y => W y j • W y) x = advection W x j := by
    rw [divergence_scalar_mul (hcoord.differentiable (by norm_num))
      (hW₁.differentiable (by norm_num)), hd x, mul_zero, zero_add]
    exact fderiv_coordinate (hW.differentiable (by simp)) x (W x) j
  have hz : (∫ x in fundamentalCube L, divergence (fun y => W y j • W y) x) = 0 :=
    integral_periodic_divergence hL (hcoord.smul hW₁)
      (show CubePeriodic L (fun y => W y j • W y) from fun x n => by dsimp only; rw [hp])
  simpa only [he] using hz

theorem ramp_force_mean_zero {L : ℝ} (hL : 0 ≤ L) {W : Space → Space}
    (hW : ContDiff ℝ ∞ W) (hp : CubePeriodic L W)
    (hd : ∀ x, divergence W x = 0)
    (hm : (∫ x in fundamentalCube L, W x) = 0)
    {α : ℝ → ℝ} (hα : Differentiable ℝ α) (ν : ℝ) :
    HasZeroMean L (residual ν (rampVelocity α W)) := by
  have hw : IntegrableOn W (fundamentalCube L) := hW.continuous.integrableOn_Icc
  have ha : IntegrableOn (advection W) (fundamentalCube L) :=
    ((hW.continuous_fderiv (by simp)).clm_apply hW.continuous).integrableOn_Icc
  have hl : IntegrableOn (laplacian W) (fundamentalCube L) :=
    (laplacian_continuous (hW.of_le (by simp))).integrableOn_Icc
  have hla : (∫ x in fundamentalCube L, laplacian W x) = 0 :=
    laplacian_mean_zero hL (hW.comp contDiff_snd)
      (show SpatiallyPeriodic L (fun y : SpaceTime => W y.2) from fun _ => hp) 0
  intro t
  simp_rw [residual_ramp ν α W (hα t)]
  have hsum := integral_add (hw.smul (deriv α t)) (ha.smul (α t ^ 2))
  simp only [Pi.smul_apply, integral_smul, hm, advection_mean_zero hL hW hp hd,
    smul_zero, add_zero] at hsum
  have hdiff := integral_sub ((hw.smul (deriv α t)).add (ha.smul (α t ^ 2)))
    ((hl.smul (α t)).smul ν)
  simpa only [Pi.add_apply, Pi.smul_apply, hsum, integral_smul, hla, smul_zero, sub_zero] using hdiff

theorem startup_force_mean_zero {L : ℝ} (hL : 0 ≤ L) {W : Space → Space}
    (hW : ContDiff ℝ ∞ W) (hp : CubePeriodic L W)
    (hd : ∀ x, divergence W x = 0)
    (hm : (∫ x in fundamentalCube L, W x) = 0) (ν : ℝ) :
    HasZeroMean L (residual ν (rampVelocity startupRamp W)) :=
  ramp_force_mean_zero hL hW hp hd hm (startupRamp_smooth.differentiable (by simp)) ν

end ForcedComputation

end

end OAI
