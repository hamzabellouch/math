import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarProcessorOrbit
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactPlanarFlow

namespace OAI

/-! A machine-only planar body for the Euclidean box test. Normalize using
one fixed empty input, then encode every other input at its own point in the
same body. The one-period realization theorems hold for every configuration. -/

noncomputable section
namespace ForcedComputation.BalancedPlanar
open ShearFlows Recorder Recorder.Planar Set

/-- The empty input fixes the spatial normalization of the repeated body. -/
def referenceInput (M : Alternating.Machine) : Alternating.MachineInput := (M, [])

theorem referenceValid {M : Alternating.Machine} (hM : M.WellFormed) :
    Alternating.ValidInput (referenceInput M) := by
  refine ⟨hM, ?_⟩
  intro a ha
  simp [referenceInput] at ha

def bodyHamiltonian (M : Alternating.Machine) (hM : M.WellFormed) : FieldExpr :=
  normalizedHamiltonian (referenceInput M) (referenceValid hM)

def bodyVelocity (M : Alternating.Machine) (hM : M.WellFormed) : ℝ → Plane → Plane :=
  compactVelocity (referenceInput M) (referenceValid hM)

def bodyCode (M : Alternating.Machine) (hM : M.WellFormed)
    (C : Configuration (State (freshMachine M)) (Alphabet (freshMachine M))) : Plane :=
  normalizedPoint (referenceInput M) (referenceValid hM) C

def inputCode (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Plane :=
  bodyCode I.1 hI.1 (finiteInitializedRecorder (freshInput I) (freshInput_valid hI))

def referenceShift (M : Alternating.Machine) (hM : M.WellFormed) : Fin 2 → ℚ :=
  initialShift (freshInput (referenceInput M)) (freshInput_valid (referenceValid hM))

theorem referenceShift_small (M : Alternating.Machine) (hM : M.WellFormed) :
    |(referenceShift M hM 0 : ℝ)| ≤ 1 / 512 ∧
      |(referenceShift M hM 1 : ℝ)| ≤ 3 / 1024 :=
  initialShift_small _ _ (fresh_initial_nonhalting _ (referenceValid hM))

theorem body_step (M : Alternating.Machine) (hM : M.WellFormed)
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition (planarSlice (bodyHamiltonian M hM)) Ψ)
    {C D : Configuration (State (freshMachine M)) (Alphabet (freshMachine M))}
    (hs : Step (finiteMachine (freshMachine M) (freshInput_valid (referenceValid hM)).1) C D) :
    Ψ 0 1 (bodyCode M hM C) = bodyCode M hM D :=
  normalized_planar_step (referenceInput M) (referenceValid hM) hΨ hs

theorem body_step_safe (M : Alternating.Machine) (hM : M.WellFormed)
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition (planarSlice (bodyHamiltonian M hM)) Ψ)
    {C D : Configuration (State (freshMachine M)) (Alphabet (freshMachine M))}
    (hs : Step (finiteMachine (freshMachine M) (freshInput_valid (referenceValid hM)).1) C D)
    (hD : recorderHalting (freshMachine M) D.control = false) {s : ℝ} (ht : s ∈ Icc (0 : ℝ) 1) :
    3 / 16 ≤ Ψ 0 s (bodyCode M hM C) 1 :=
  normalized_step_safe (referenceInput M) (referenceValid hM) hΨ hs hD ht

theorem body_step_corridor (M : Alternating.Machine) (hM : M.WellFormed)
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition (planarSlice (bodyHamiltonian M hM)) Ψ)
    {C D : Configuration (State (freshMachine M)) (Alphabet (freshMachine M))}
    (hs : Step (finiteMachine (freshMachine M) (freshInput_valid (referenceValid hM)).1) C D)
    {s : ℝ} (ht : s ∈ Icc (0 : ℝ) 1) :
    Ψ 0 s (bodyCode M hM C) ∈ clockRectangle.carrier :=
  normalized_step_corridor (referenceInput M) (referenceValid hM) hΨ hs ht

theorem body_observation (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (bodyHamiltonian I.1 hI.1)) Ψ) :
    (∃ t : ℝ, 0 ≤ t ∧ Ψ 0 t (inputCode I hI) ∈ observer) ↔ Alternating.Halts I := by
  have hδ := (referenceShift_small I.1 hI.1).2
  have h := shifted_planar_observation (freshInput I) (freshInput_valid hI)
    (referenceShift I.1 hI.1) hδ hΨ
    (planarSlice_periodic (normalizedHamiltonian_periodic
      (referenceInput I.1) (referenceValid hI.1)))
    (body_step I.1 hI.1 hΨ)
    (fun {C D} hs _ hD s ht => body_step_safe I.1 hI.1 hΨ hs hD ht)
  exact h.trans (freshInput_halts_iff hI)

end ForcedComputation.BalancedPlanar

end

end OAI
