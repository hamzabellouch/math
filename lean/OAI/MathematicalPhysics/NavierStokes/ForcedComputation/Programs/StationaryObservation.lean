import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NormalizedSuspensionRouting
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarDormantZero
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarStepBranch
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SuspensionObservation

namespace OAI

/-! Exact machine steps and all-time nonhalting exclusion for the actual
normalized autonomous suspension. All geometric obligations are proved
from the finite compiler; no routing hypothesis remains in these statements. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows PlanarRouting Set

theorem normalized_suspension_step (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y =>
      SpatialExpression.suspensionField (normalizedHamiltonian I hI) y.2) Φ)
    {C D : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))}
    (hstep : Step (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) C D) :
    Φ 1 (atHeight (shiftPoint (initialShift (freshInput I) (freshInput_valid hI))
      (point (freshMachine I.1) (freshInput_valid hI).1 C)) 0) =
      atHeight (shiftPoint (initialShift (freshInput I) (freshInput_valid hI))
        (point (freshMachine I.1) (freshInput_valid hI).1 D)) 1 := by
  obtain ⟨b, _, _, hx, he⟩ := step_branch hstep
  have h := normalized_branch_suspension I hI b hx hΦ
  simpa [normalizedAnchors, branchAnchors_first, branchAnchors_last, he, translatedPoint_eq_shiftPoint] using h.1

theorem normalized_suspension_step_safe (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y =>
      SpatialExpression.suspensionField (normalizedHamiltonian I hI) y.2) Φ)
    {C D : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))}
    (hstep : Step (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) C D)
    (hD : recorderHalting (freshMachine I.1) D.control = false)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    3 / 16 ≤ Φ s (atHeight (shiftPoint (initialShift (freshInput I) (freshInput_valid hI))
      (point (freshMachine I.1) (freshInput_valid hI).1 C)) 0) 1 := by
  obtain ⟨b, _, ht, hx, _⟩ := step_branch hstep
  have hn : recorderHalting (freshMachine I.1) b.target = false := by rw [ht]; exact hD
  have h := normalized_branch_suspension_safe I hI b hn hx hΦ
  simpa [normalizedAnchors, branchAnchors_first, translatedPoint_eq_shiftPoint, horizontal] using (h.2 s hs).2

theorem stationary_suspension_observation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y =>
      SpatialExpression.suspensionField (normalizedHamiltonian I hI) y.2) Φ) :
    Reaches (fun t => Φ t stationaryStartingPoint) stationaryObserver ↔ Alternating.Halts I := by
  apply normalized_suspension_observation I hI hΦ
  · intro C D hstep
    exact normalized_suspension_step I hI hΦ hstep
  · intro C D hstep _ hD s hs
    exact normalized_suspension_step_safe I hI hΦ hstep hD s hs

end ForcedComputation.Recorder.Planar

end

end OAI
