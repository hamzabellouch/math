import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.MachineDecisionInput
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TorusDetectorMain
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingMain

namespace OAI

/-! Decision corollaries for the prescribed forces and their actual classical
solutions. The observation predicates mention neither machines nor halting. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory ExpandingDetector
open scoped ContDiff

def TorusVelocityEvent (ν : ℝ) (f : Velocity) : Prop :=
  ∃ u p, IsClassicalSolution 1 ν f u p ∧
    ∃ t, 0 ≤ t ∧ ∃ x : Space, 1 / 32 < x 1 ∧ x 1 < 1 / 8 ∧ 1 / 2 < u (t,x) 2

def compiledTorusDetectorForce (ν : ℝ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity :=
  let H := Recorder.Planar.normalizedHamiltonian I hI
  detectorViscosityForce (planarSlice H) detectorBumpDerivativeBound (euclideanFlowBound H) ν

theorem torus_velocity_event_iff (hE : TorusScalarExistence) (hK : TorusHeatInput)
    (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (Ω : ℝ → ℝ → Plane → Plane)
    (hΩ : IsPlanarTransition (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) Ω)
    (hv : PlanarVariations (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) Ω)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ω y.1 (-y.1) y.2))
    {ν : ℝ} (hν : 0 < ν) :
    TorusVelocityEvent ν (compiledTorusDetectorForce ν I hI) ↔ Alternating.Halts I := by
  obtain ⟨_, _, w, _, _, _, hall⟩ := torus_velocity_detection hE hK I hI Ω hΩ hv hback
  obtain ⟨_, _, _, hsol, huniq, hobs, _, _, _⟩ := hall ν hν
  constructor
  · rintro ⟨u, p, hu, t, ht, x, hx₁, hx₂, hx⟩
    apply hobs.mp
    exact ⟨t, ht, x, hx₁, hx₂, by simpa only [(huniq u p hu t ht x).1] using hx⟩
  · intro hh
    exact ⟨_, _, hsol, hobs.mpr hh⟩

/-- The compact-chart velocity event is undecidable on the finite source inputs. -/
theorem torus_velocity_undecidable (hT : FiniteMachineHaltingUndecidable)
    (hE : TorusScalarExistence) (hK : TorusHeatInput)
    (hv : ∀ I hI Ω,
      IsPlanarTransition (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) Ω →
      PlanarVariations (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) Ω)
    (hback : ∀ I hI Ω,
      IsPlanarTransition (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) Ω →
      ContDiff ℝ ∞ (fun y : ℝ × Plane => Ω y.1 (-y.1) y.2))
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      TorusVelocityEvent ν (compiledTorusDetectorForce ν I hI)) := by
  apply noCompiledInputDecider_of_halting hT
  intro I hI
  obtain ⟨Ω, hΩ⟩ := exists_planarTransition
    (Recorder.Planar.normalizedHamiltonian_valid I hI)
    (Recorder.Planar.normalizedHamiltonian_noTime I hI)
  exact torus_velocity_event_iff hE hK I hI Ω hΩ (hv I hI Ω hΩ) (hback I hI Ω hΩ) hν

def PlaneVelocityEvent (ν : ℝ) (f : Velocity) : Prop :=
  ∃ u p, IsCylinderClassicalSolution ν f u p ∧
    ∃ t, 0 ≤ t ∧ 1 / 2 < upperCylinderMass u t

theorem plane_velocity_event_iff {ν : ℝ} {f : Velocity} {I : Alternating.MachineInput}
    (hd : ExpandingDetector.WholePlaneDetection ν f I) :
    PlaneVelocityEvent ν f ↔ Alternating.Halts I := by
  obtain ⟨u, _, hu, huniq, _, _, _, hobs⟩ := hd
  constructor
  · rintro ⟨v, p, hv, t, ht, hmass⟩
    apply hobs.mp
    refine ⟨t, ht, ?_⟩
    have he (x : Space) : v (t,x) = u (t,x) := (huniq v p hv t ht x).1
    simpa only [upperCylinderMass, he] using hmass
  · intro hh
    exact ⟨u, _, hu, hobs.mpr hh⟩

/-- The whole-plane integral event is undecidable for every positive viscosity. -/
theorem plane_velocity_undecidable (hT : FiniteMachineHaltingUndecidable)
    (hE : PlaneScalarExistence) (hEnergy : CylinderLocalEnergyIdentity) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (ν : ℝ), 0 < ν → ∀ (a : ℕ → ℚ), IsFastRealName a ν →
      NoCompiledInputDecider (fun I hI =>
        PlaneVelocityEvent ν (ExpandingDetector.compiledExpandingForce C I hI a ν)) := by
  obtain ⟨C, hC, hall⟩ := ExpandingDetector.whole_plane_velocity_detection hE hEnergy
  refine ⟨C, hC, ?_⟩
  intro ν hν a ha
  apply noCompiledInputDecider_of_halting hT
  intro I hI
  obtain ⟨_, _, _, _, _, hd⟩ := hall I hI ν hν a ha
  exact plane_velocity_event_iff hd

end ForcedComputation.VelocityDetector

end

end OAI
