import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RapidDecisionCorollaries
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RapidMachineHaltingDischarge

namespace OAI

/-! The four primary rapid-forcing decision results with the finite-machine
undecidability inputs discharged. -/

noncomputable section
namespace ForcedComputation

theorem rapid_particle_undecidable_unconditional :
    ¬ ∃ d : ℕ → Bool, Computable d ∧
      ∀ (M : RapidForcing.Machine) (w : M.Input),
        d (M.inputDescription w) = true ↔
          RapidMaterialEvent (RapidForcing.addressedVelocity M w) :=
  rapid_particle_undecidable rapidMachineHaltingUndecidable

theorem alternating_particle_undecidable_unconditional :
    ¬ ∃ d : AlternatingNS.Machine × List ℕ → Bool, Computable d ∧
      ∀ (M : AlternatingNS.Machine) (w : List ℕ), M.WellFormed → M.ValidInput w →
        (d (M,w) = true ↔ AlternatingMaterialEvent (AlternatingNS.Construction.velocity M w)) :=
  alternating_particle_undecidable alternatingMachineHaltingUndecidable

theorem lattice_particle_undecidable_unconditional :
    ¬ ∃ d : PeriodicLattice.Input → Bool, Computable d ∧
      ∀ I : PeriodicLattice.Input, I.WellFormed → (d I = true ↔ LatticeMaterialEvent (PeriodicLattice.FluidLift.velocity I)) :=
  lattice_particle_undecidable latticeMachineHaltingUndecidable

theorem rapid_torus_particle_undecidable_unconditional :
    ¬ ∃ d : PeriodicLattice.Input → Bool, Computable d ∧
      ∀ I : PeriodicLattice.Input, I.WellFormed → (d I = true ↔ RapidTorusMaterialEvent
        (PeriodicLattice.RapidTorus.transformedField (PeriodicLattice.FluidLift.velocity I))) :=
  rapid_torus_particle_undecidable latticeMachineHaltingUndecidable

end ForcedComputation

end

end OAI
