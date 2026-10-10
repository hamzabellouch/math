import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StationaryBounds

namespace OAI

/-! The complete analytic bundle for a smooth periodic autonomous field
started from rest. The finite planar processor is supplied separately. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set MeasureTheory
open scoped ContDiff

structure StationaryFluidProperties (L ν : ℝ) (U : Velocity) : Prop where
  velocity_smooth : ContDiff ℝ ∞ U
  force_smooth : ContDiff ℝ ∞ (residual ν U)
  velocity_periodic : SpatiallyPeriodic L U
  force_periodic : SpatiallyPeriodic L (residual ν U)
  velocity_solenoidal : Solenoidal U
  velocity_mean : HasZeroMean L U
  force_mean : HasZeroMean L (residual ν U)
  velocity_bounds : BoundedMixedDerivatives U
  force_bounds : BoundedMixedDerivatives (residual ν U)
  energy_bound : ∃ E : ℝ, ∀ t, kineticEnergy L U t ≤ E
  velocity_tail : ∀ t, 1 ≤ t → ∀ x, U (t, x) = U (1, x)
  force_tail : ∀ t, 1 ≤ t → ∀ x, residual ν U (t, x) = residual ν U (1, x)
  solution : IsClassicalSolution L ν (residual ν U) U (fun _ => 0)
  unique : ∀ u p, IsClassicalSolution L ν (residual ν U) u p →
    ∀ t, 0 ≤ t → ∀ x, u (t, x) = U (t, x) ∧ p (t, x) = 0

theorem startup_bundle {L ν : ℝ} (hL : 0 < L) (hν : 0 ≤ ν)
    {W : Space → Space} (hW : ContDiff ℝ ∞ W)
    (hp : CubePeriodic L W) (hd : ∀ x, divergence W x = 0)
    (hm : (∫ x in fundamentalCube L, W x) = 0) :
    StationaryFluidProperties L ν (rampVelocity startupRamp W) := by
  have hs := ramp_smooth startupRamp_smooth hW
  have hsp := ramp_periodic startupRamp hp
  have hb := startup_bounds hL hW hp ν
  have hsol := startup_solution hW hp hd ν
  refine ⟨hs, residual_smooth hs ν, hsp, residual_spatially_periodic hs hsp ν,
    ramp_solenoidal startupRamp hd, ?_, startup_force_mean_zero hL.le hW hp hd hm ν,
    hb.1, hb.2, startup_energy_bounded hL hW hp, ?_, ?_, hsol.2.2.1,
    startup_solution_unique hL hν hW hp hd⟩
  · intro t
    change (∫ x in fundamentalCube L, startupRamp t • W x) = 0
    rw [integral_smul, hm, smul_zero]
  · intro t ht x
    simp only [rampVelocity, startupRamp_tail ht, startupRamp_tail le_rfl, one_smul]
  · intro t ht x
    rw [hsol.2.2.2 t ht x, hsol.2.2.2 1 le_rfl x]

/-- Startup preserves the actual autonomous material trajectories, with an
onto nonnegative clock. The statement applies to every chosen particle and
observation set at once. -/
theorem startup_bundle_with_flow {L ν : ℝ} (hL : 0 < L) (hν : 0 ≤ ν)
    {W : Space → Space} (hW : ContDiff ℝ ∞ W)
    (hp : CubePeriodic L W) (hd : ∀ x, divergence W x = 0)
    (hm : (∫ x in fundamentalCube L, W x) = 0) :
    StationaryFluidProperties L ν (rampVelocity startupRamp W) ∧
      ∃ Φ : ℝ → Space → Space,
        IsMaterialFlow L (fun y => W y.2) Φ ∧
        IsMaterialFlow L (rampVelocity startupRamp W)
          (fun t x => Φ (accumulatedClock startupRamp t) x) ∧
        ∀ x O, Reaches (fun t => Φ (accumulatedClock startupRamp t) x) O ↔
          Reaches (fun t => Φ t x) O :=
  ⟨startup_bundle hL hν hW hp hd hm, startup_materialFlow hL hW hp⟩

end ForcedComputation

end

end OAI
