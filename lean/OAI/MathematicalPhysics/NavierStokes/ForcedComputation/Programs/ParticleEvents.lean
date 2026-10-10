import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.MachineDecisionInput
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedMain
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FixedParticleMain
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StationaryMain
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TorusSlowMain
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PrefixMain
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicMain

namespace OAI

/-! Decision corollaries for the actual compiled fluid experiments.
The sole new premise is the separately cited finite-machine halting input.
The particle events and their equivalence to halting are proved from the
compiled Navier–Stokes main results, including uniqueness of material flow.
-/

noncomputable section
namespace ForcedComputation
open ShearFlows Set

/-- The designated particle of the prescribed fluid enters the open set. -/
def MaterialEvent (V : Velocity) (a : Space) (O : Set Space) : Prop :=
  ∃ Φ : ℝ → Space → Space, IsMaterialFlow 1 V Φ ∧ Reaches (fun t => Φ t a) O

theorem materialEvent_iff {V : Velocity} {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 V Φ) (a : Space) (O : Set Space) :
    MaterialEvent V a O ↔ Reaches (fun t => Φ t a) O := by
  constructor
  · rintro ⟨Ψ, hΨ, t, ht, hx⟩
    have he : Ψ t a = Φ t a :=
      hΦ.unique a (fun s => Ψ s a) (hΨ.initial a) (fun s => hΨ.ode s a) t
    exact ⟨t, ht, by simpa only [he] using hx⟩
  · intro h
    exact ⟨Φ, hΦ, h⟩

def particleRightHalf : Set Space := {x | 1 / 2 < x 0 ∧ x 0 < 1}

theorem initialized_material_event_iff (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {ν : ℝ} (hν : 0 < ν) :
    MaterialEvent (machineVelocity I hI) ![1 / 8, 3 / 8, 1 / 2] particleRightHalf ↔
      Alternating.Halts I := by
  obtain ⟨_, _, _, Φ, hΦ, he⟩ := initialized_effective_computation I hI ν hν
  exact (materialEvent_iff hΦ _ _).trans (by
    simpa only [Reaches, particleRightHalf, mem_ofPred_eq] using he.symm)

theorem fixed_particle_material_event_iff (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {ν : ℝ} (hν : 0 < ν) :
    MaterialEvent (fixedParticleVelocity I hI) ![1 / 8, 3 / 8, 0] particleRightHalf ↔
      Alternating.Halts I := by
  obtain ⟨_, _, _, Φ, hΦ, he⟩ := fixed_particle_effective_computation I hI ν hν
  exact (materialEvent_iff hΦ _ _).trans (by
    simpa only [Reaches, particleRightHalf, mem_ofPred_eq] using he.symm)

theorem stationary_material_event_iff (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {ν : ℝ} (hν : 0 < ν) :
    MaterialEvent (stationaryVelocity I hI) stationaryStartingPoint
      stationaryObserver ↔ Alternating.Halts I := by
  obtain ⟨_, _, _, _, _, Φ, hΦ, he⟩ := stationary_effective_computation I hI ν hν
  exact (materialEvent_iff hΦ _ _).trans he

theorem slow_material_event_iff (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {ν : ℝ} (hν : 0 < ν) :
    MaterialEvent (torusSlowVelocity I hI) ![1 / 4, 1 / 2, 1 / 2] particleRightHalf ↔
      Alternating.Halts I := by
  obtain ⟨_, _, _, _, Φ, hΦ, he⟩ := torus_slow_effective_computation I hI ν hν
  exact (materialEvent_iff hΦ _ _).trans (by
    simpa only [Reaches, particleRightHalf, mem_ofPred_eq] using he.symm)

theorem prefix_material_event_iff (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {ν : ℝ} (hν : 0 < ν) :
    MaterialEvent (prefixVelocity I hI) ![1 / 8, 1 / 4, 1 / 4] particleRightHalf ↔
      Alternating.Halts I := by
  obtain ⟨_, _, _, Φ, hΦ, he⟩ := prefix_effective_computation I hI ν hν
  exact (materialEvent_iff hΦ _ _).trans (by
    simpa only [Reaches, particleRightHalf, mem_ofPred_eq] using he.symm)

theorem periodic_material_event_iff (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {ν : ℝ} (hν : 0 < ν) :
    MaterialEvent (periodicVelocity I hI) ![1 / 4, 1 / 2, 1 / 4]
      {x | 1 / 2 < x 0 ∧ x 0 < 7 / 8} ↔ Alternating.Halts I := by
  obtain ⟨_, _, _, _, Φ, hΦ, he⟩ := periodic_effective_computation I hI ν hν
  exact (materialEvent_iff hΦ _ _).trans (by
    simpa only [Reaches, mem_ofPred_eq] using he.symm)

end ForcedComputation

end

end OAI
