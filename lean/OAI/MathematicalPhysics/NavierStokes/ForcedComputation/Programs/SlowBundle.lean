import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowFluid

namespace OAI

/-! Analytic bundle for the square-integrable fixed-particle construction. -/

namespace ForcedComputation
open ShearFlows
open scoped ContDiff NNReal

def SlowFluidProperties (L ν : ℝ) (U : Velocity) : Prop :=
  ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ (force ν U) ∧
  SpatiallyPeriodic L U ∧ SpatiallyPeriodic L (force ν U) ∧
  Solenoidal U ∧ Solenoidal (force ν U) ∧
  HasZeroMean L U ∧ HasZeroMean L (force ν U) ∧
  UniformMixedL2 U ∧ UniformMixedL2 (force ν U) ∧
  (∃ E : ℝ, ∀ t, kineticEnergy L U t ≤ E) ∧
  IsClassicalSolution L ν (force ν U) U (fun _ => 0) ∧
  (∀ u p, IsClassicalSolution L ν (force ν U) u p →
    ∀ t, 0 ≤ t → ∀ x, u (t, x) = U (t, x) ∧ p (t, x) = 0)

theorem slow_initialized_bundle {loader body : Input}
    (hl : ValidInput loader) (hb : ValidInput body)
    (hp : loader.period = body.period) (ν : ℝ) (hν : 0 ≤ ν) :
    SlowFluidProperties body.period ν (slowFromRest (initializedProgram loader body)) := by
  let V := initializedProgram loader body
  have hs : ContDiff ℝ ∞ V := initializedProgram_smooth hl hb
  have hz : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0 :=
    fun _ ht x => initializedProgram_zero_extend loader body ht x
  have hper : SpatiallyPeriodic body.period V := initializedProgram_periodic hp
  have hdiv : Solenoidal V := initializedProgram_solenoidal hl hb
  have hadv : ZeroAdvection V := initializedProgram_zero_advection hl hb
  have hbounded : BoundedMixedDerivatives V := initializedProgram_bounded hl hb hp
  have hslow := slowFromRest_smooth hs hz
  have hslowper := slowFromRest_periodic hper
  obtain ⟨hUL2, hFL2⟩ := slowFromRest_uniformMixedL2 hs hz hbounded hadv ν
  obtain ⟨K, hK⟩ := initializedProgram_spatial_lipschitz hl hb
  refine ⟨hslow, force_smooth hslow ν, hslowper,
    force_spatially_periodic hslow hslowper ν, slowFromRest_solenoidal hdiv,
    force_solenoidal hslow (slowFromRest_solenoidal hdiv) ν,
    slowFromRest_mean_zero (initializedProgram_mean_zero hl hb hp),
    slowFromRest_force_mean_zero (by exact_mod_cast hb.period_pos.le) hs hper hz hadv
      (initializedProgram_mean_zero hl hb hp) (initializedForce_mean_zero hl hb hp 0) ν,
    hUL2, hFL2, slowFromRest_energy hs hz hbounded,
    slowFromRest_solution hs hper hz hdiv hadv ν,
    slowFromRest_unique (by exact_mod_cast hb.period_pos) hν hs hper hz hdiv hadv hK⟩

end ForcedComputation

end OAI
