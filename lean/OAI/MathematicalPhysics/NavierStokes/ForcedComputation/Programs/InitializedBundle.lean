import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedEffective

namespace OAI

/-! Fluid regularity for a finite loading program followed by a periodic
machine program. -/

namespace ForcedComputation
open ShearFlows
open scoped ContDiff

def InitializedFluidProperties (L ν : ℝ) (U : Velocity) : Prop :=
  letI := ShearFlows.thirtyTwoAtLeastTwo
  ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ (force ν U) ∧
  SpatiallyPeriodic L U ∧ SpatiallyPeriodic L (force ν U) ∧
  Solenoidal U ∧ Solenoidal (force ν U) ∧
  HasZeroMean L U ∧ HasZeroMean L (force ν U) ∧
  BoundedMixedDerivatives U ∧ BoundedMixedDerivatives (force ν U) ∧
  (∀ t x, 1 ≤ t → U (t + 1, x) = U (t, x) ∧ force ν U (t + 1, x) = force ν U (t, x)) ∧
  (∀ k : ℤ, ∀ t : ℝ, |t - (k : ℝ)| < (1 / 32 : ℝ) → ∀ x,
    U (t, x) = 0 ∧ force ν U (t, x) = 0) ∧
  (∃ E : ℝ, ∀ t, kineticEnergy L U t ≤ E) ∧
  IsClassicalSolution L ν (force ν U) U (fun _ => 0) ∧
  (∀ u p, IsClassicalSolution L ν (force ν U) u p →
    ∀ t, 0 ≤ t → ∀ x, u (t, x) = U (t, x) ∧ p (t, x) = 0)

theorem initialized_bundle {loader body : Input}
    (hl : ValidInput loader) (hb : ValidInput body)
    (hp : loader.period = body.period) (ν : ℝ) (hν : 0 ≤ ν) :
    InitializedFluidProperties body.period ν (initializedProgram loader body) := by
  have hs := initializedProgram_smooth hl hb
  refine ⟨hs, force_smooth hs ν, initializedProgram_periodic hp,
    force_spatially_periodic hs (initializedProgram_periodic hp) ν,
    initializedProgram_solenoidal hl hb, initializedForce_solenoidal hl hb ν,
    initializedProgram_mean_zero hl hb hp, initializedForce_mean_zero hl hb hp ν,
    initializedProgram_bounded hl hb hp, initializedForce_bounded hl hb hp ν,
    ?_, ?_, initializedProgram_energy_bounded hl hb hp,
    initializedProgram_solution hl hb hp ν, initializedProgram_unique hl hb hp hν⟩
  · intro t x ht
    exact ⟨initializedProgram_eventually_periodic loader body ht x,
      initializedForce_eventually_periodic hl hb ν ht x⟩
  · intro k t ht x
    exact ⟨initializedProgram_integer_collars loader body k ht x,
      initializedForce_integer_collars hl hb ν k ht x⟩

end ForcedComputation

end OAI
