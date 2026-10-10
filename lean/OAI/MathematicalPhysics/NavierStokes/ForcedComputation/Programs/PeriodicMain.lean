import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicObservation
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ForceEvaluation

namespace OAI

/-! The periodic-initialization main theorem of *Geometric Programs for
Solenoidal Forcing*. The finite program repeats its loading instruction, but
the fresh recorder never returns to that instruction's source or target. -/

namespace ForcedComputation
open ShearFlows Recorder
open scoped ContDiff

def PeriodicFluidProperties (L ν : ℝ) (U : Velocity) : Prop :=
  ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ (force ν U) ∧
  SpatiallyPeriodic L U ∧ SpatiallyPeriodic L (force ν U) ∧
  Solenoidal U ∧ Solenoidal (force ν U) ∧
  HasZeroMean L U ∧ HasZeroMean L (force ν U) ∧
  TimePeriodic U ∧ TimePeriodic (force ν U) ∧ ZeroAdvection U ∧
  BoundedMixedDerivatives U ∧ BoundedMixedDerivatives (force ν U) ∧
  (∀ k : ℤ, ∀ t : ℝ, |t - (k : ℝ)| < (1 / 32 : ℝ) → ∀ x, U (t, x) = 0) ∧
  (∃ E : ℝ, ∀ t, kineticEnergy L U t ≤ E) ∧
  IsClassicalSolution L ν (force ν U) U (fun _ => 0) ∧
  (∀ u p, IsClassicalSolution L ν (force ν U) u p →
    ∀ t, 0 ≤ t → ∀ x, u (t, x) = U (t, x) ∧ p (t, x) = 0)

theorem periodic_bundle {d : Input} (hd : ValidInput d) (ν : ℝ) (hν : 0 < ν) :
    PeriodicFluidProperties d.period ν d.realizingVelocity := by
  have hs := realizingVelocity_smooth hd
  have hp := realizingVelocity_spatially_periodic d
  have ht := realizingVelocity_time_periodic d
  have hz := realizingVelocity_divergence_advection hd
  exact ⟨hs, force_smooth hs ν, hp, force_spatially_periodic hs hp ν,
    hz.1, force_solenoidal hs hz.1 ν, realizingVelocity_mean_zero hd,
    realizingForce_mean_zero hd ν, ht, force_time_periodic hs ht ν, hz.2,
    realizingVelocity_boundedMixedDerivatives hd,
    force_boundedMixedDerivatives (by exact_mod_cast hd.period_pos) hs hp ht ν,
    fun k t hk x => realizingVelocity_vanish_near_integers d k hk x,
    realizingVelocity_kineticEnergy_bound hd, realizingVelocity_solves_NS hd ν,
    realizingVelocity_unique hd hν⟩

def periodicProgram (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Input :=
  periodicInitializedInput I hI

noncomputable def periodicVelocity (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity := (periodicProgram I hI).realizingVelocity

noncomputable def periodicForce (ν : ℝ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity := force ν (periodicVelocity I hI)

theorem periodic_effective_computation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (hν : 0 < ν) :
    PeriodicFluidProperties 1 ν (periodicVelocity I hI) ∧
    HasEffectiveDerivatives (periodicVelocity I hI) (periodicProgram I hI).velocityExpr ∧
    HasEffectiveForce ν (periodicVelocity I hI) (periodicProgram I hI).velocityExpr ∧
    (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime) (y : SpaceTime),
      IsFastRealName a ν → IsFastName b y → ∀ (ε : ℚ) (hε : 0 < ε),
        ‖mixedDerivative (periodicForce ν I hI) α y -
          rationalVector ((periodicProgram I hI).velocityExpr.evaluateForce
            (velocityExpr_valid (periodicInitializedInput_valid I hI)) α a b ε hε)‖ ≤ (ε : ℝ)) ∧
    ∃ Φ : ℝ → Space → Space, IsMaterialFlow 1 (periodicVelocity I hI) Φ ∧
      (Alternating.Halts I ↔ ∃ t : ℝ, 0 ≤ t ∧
        1 / 2 < Φ t ![1 / 4, 1 / 2, 1 / 4] 0 ∧
        Φ t ![1 / 4, 1 / 2, 1 / 4] 0 < 7 / 8) := by
  have hd := periodicInitializedInput_valid I hI
  have hp := periodic_bundle hd ν hν
  refine ⟨by simpa [periodicVelocity, periodicProgram] using hp, ?_, ?_, ?_, ?_⟩
  · simpa only [periodicVelocity, periodicProgram, compileShears] using compileShears_effective hd
  · simpa only [periodicVelocity, periodicProgram, compileShears] using compileShears_force_effective hd ν
  · intro α a b y ha hb ε hε
    simpa only [periodicForce, periodicVelocity, periodicProgram, ← velocityExpr_val hd] using
      VelocityExpr.evaluateForce_spec (velocityExpr_valid hd) α ha hb ε hε
  · obtain ⟨Φ, hΦ⟩ := realizingVelocity_materialFlow hd
    refine ⟨Φ, by simpa [periodicVelocity, periodicProgram] using hΦ, ?_⟩
    simpa only [periodicStartingPoint] using (periodic_flow_halting_iff I hI hΦ).symm

end ForcedComputation

end OAI
