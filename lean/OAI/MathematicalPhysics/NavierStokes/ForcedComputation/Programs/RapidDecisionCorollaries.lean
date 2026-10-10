import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RapidMachineDecisionInput
import OAI.MathematicalPhysics.RapidForcing.Main
import OAI.MathematicalPhysics.AlternatingFlow.Development
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicLatticeCorollaryMain

namespace OAI

/-! The four undecidable material experiments in paper 379-06. Their events
refer only to actual material paths and fixed open observation sets. -/

noncomputable section
namespace ForcedComputation

open Set

def RapidMaterialEvent (u : RapidForcing.Field RapidForcing.Space) : Prop :=
  ∃ X : ℝ → RapidForcing.Space → RapidForcing.Space,
    RapidForcing.MaterialFlow u X ∧ ∃ t, 0 ≤ t ∧ (X t 0) 0 < -1

theorem rapid_material_event_iff (M : RapidForcing.Machine) (w : M.Input) :
    RapidMaterialEvent (RapidForcing.addressedVelocity M w) ↔ M.Halts w := by
  constructor
  · rintro ⟨X, hX, he⟩
    exact (RapidForcing.materialFlow_halting_iff M w hX).mpr he
  · intro hh
    obtain ⟨X, hX⟩ := RapidForcing.addressed_materialFlow M w
    exact ⟨X, hX, (RapidForcing.materialFlow_halting_iff M w hX).mp hh⟩

/-- The compact Euclidean rapid-force experiment has no total decider. -/
theorem rapid_particle_undecidable (hT : RapidMachineHaltingUndecidable) :
    ¬ ∃ d : ℕ → Bool, Computable d ∧
      ∀ (M : RapidForcing.Machine) (w : M.Input),
        d (M.inputDescription w) = true ↔
          RapidMaterialEvent (RapidForcing.addressedVelocity M w) := by
  rintro ⟨d, hd, he⟩
  exact hT ⟨d, hd, fun M w => (he M w).trans (rapid_material_event_iff M w)⟩

def AlternatingMaterialEvent (u : AlternatingNS.Velocity) : Prop :=
  ∃ γ : ℝ → AlternatingNS.Space,
    AlternatingNS.IsTrajectory u AlternatingNS.observedParticle γ ∧
    ∃ t, 0 ≤ t ∧ 0 < γ t 0

theorem alternating_material_event_iff (M : AlternatingNS.Machine) (w : List ℕ)
    (hM : M.WellFormed) (hw : M.ValidInput w) :
    AlternatingMaterialEvent (AlternatingNS.Construction.velocity M w) ↔ M.Halts w := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, X, hX, huniq, hhalt⟩ :=
    AlternatingNS.Construction.alternating_analytic 1 (by norm_num) M w hM hw
  constructor
  · rintro ⟨γ, hγ, t, ht, he⟩
    exact hhalt.mp ⟨t, ht, by simpa only [huniq _ _ hγ t ht] using he⟩
  · intro hh
    obtain ⟨t, ht, he⟩ := hhalt.mpr hh
    exact ⟨X AlternatingNS.observedParticle, hX _, t, ht, he⟩

/-- The alternating-memory rapid-force experiment has no total decider. -/
theorem alternating_particle_undecidable (hT : AlternatingMachineHaltingUndecidable) :
    ¬ ∃ d : AlternatingNS.Machine × List ℕ → Bool, Computable d ∧
      ∀ (M : AlternatingNS.Machine) (w : List ℕ), M.WellFormed → M.ValidInput w →
        (d (M,w) = true ↔ AlternatingMaterialEvent (AlternatingNS.Construction.velocity M w)) := by
  rintro ⟨d, hd, he⟩
  exact hT ⟨d, hd, fun M w hM hw =>
    (he M w hM hw).trans (alternating_material_event_iff M w hM hw)⟩

def LatticeMaterialEvent (u : PeriodicLattice.VectorField) : Prop :=
  ∃ γ, PeriodicLattice.IsParticle u γ ∧ PeriodicLattice.MaterialEvent γ

def RapidTorusMaterialEvent (u : PeriodicLattice.VectorField) : Prop :=
  ∃ γ, PeriodicLattice.RapidTorus.IsCorollaryParticle u γ ∧
    ∃ t, 0 ≤ t ∧ PeriodicLattice.torusMk (γ t) ∈ PeriodicLattice.RapidTorus.corollaryDetector

theorem lattice_material_event_iff (I : PeriodicLattice.Input) (hI : I.WellFormed) :
    LatticeMaterialEvent (PeriodicLattice.FluidLift.velocity I) ↔ PeriodicLattice.Halts I := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, X, hX, huniq, he⟩ :=
    PeriodicLattice.FluidLift.analytic_lattice_conclusion 1 (by norm_num) I hI
  constructor
  · rintro ⟨γ, hγ, t, ht, hobs⟩
    exact he.mp ⟨t, ht, by simpa only [huniq γ hγ t ht] using hobs⟩
  · intro hh
    exact ⟨X, hX, he.mpr hh⟩

theorem rapid_torus_material_event_iff (I : PeriodicLattice.Input) (hI : I.WellFormed) :
    RapidTorusMaterialEvent
      (PeriodicLattice.RapidTorus.transformedField (PeriodicLattice.FluidLift.velocity I)) ↔
      PeriodicLattice.Halts I := by
  constructor
  · rintro ⟨γ, hγ, t, ht, hobs⟩
    apply (PeriodicLattice.RapidTorus.transformed_path_event I hI).mp
    exact ⟨t, ht, by
      simpa only [PeriodicLattice.RapidTorus.corollaryPath_unique I hI hγ.1 hγ.2 ht,
        PeriodicLattice.RapidTorus.corollaryPath] using hobs⟩
  · intro hh
    refine ⟨PeriodicLattice.RapidTorus.corollaryPath I, ?_,
      (PeriodicLattice.RapidTorus.transformed_path_event I hI).mpr hh⟩
    exact ⟨PeriodicLattice.RapidTorus.corollaryPath_start I, fun t ht =>
      (PeriodicLattice.RapidTorus.corollaryPath_hasDerivAt I hI ht).hasDerivWithinAt⟩

/-- Both general and solenoidal lattice forces drive this same material event. -/
theorem lattice_particle_undecidable (hT : LatticeMachineHaltingUndecidable) :
    ¬ ∃ d : PeriodicLattice.Input → Bool, Computable d ∧
      ∀ I : PeriodicLattice.Input, I.WellFormed → (d I = true ↔ LatticeMaterialEvent (PeriodicLattice.FluidLift.velocity I)) := by
  rintro ⟨d, hd, he⟩
  exact hT ⟨d, hd, fun I hI => (he I hI).trans (lattice_material_event_iff I hI)⟩

/-- The solenoidal mean-zero rapid-force experiment on the torus is undecidable. -/
theorem rapid_torus_particle_undecidable (hT : LatticeMachineHaltingUndecidable) :
    ¬ ∃ d : PeriodicLattice.Input → Bool, Computable d ∧
      ∀ I : PeriodicLattice.Input, I.WellFormed → (d I = true ↔ RapidTorusMaterialEvent
        (PeriodicLattice.RapidTorus.transformedField (PeriodicLattice.FluidLift.velocity I))) := by
  rintro ⟨d, hd, he⟩
  exact hT ⟨d, hd, fun I hI => (he I hI).trans (rapid_torus_material_event_iff I hI)⟩

end ForcedComputation

end

end OAI
