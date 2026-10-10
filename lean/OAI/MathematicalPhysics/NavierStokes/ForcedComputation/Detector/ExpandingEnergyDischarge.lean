import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingMain
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderEnergyIdentity

namespace OAI

/-! The whole-plane main result with its localized energy input discharged.
Only the published scalar existence input remains explicit. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set
open scoped ContDiff

theorem whole_plane_velocity_detection_energy_discharged (hE : PlaneScalarExistence)
    :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
      (ν : ℝ), 0 < ν → ∀ (a : ℕ → ℚ), IsFastRealName a ν →
      let f := compiledExpandingForce C I hI a ν
      ContDiff ℝ ∞ f ∧
      (∀ α : List (Fin 4), ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖mixedDerivative f α y‖ ≤ B) ∧
      (∀ T : ℝ, ∃ K : Set Plane, IsCompact K ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space, horizontalLinear x ∉ K → f (t,x) = 0) ∧
      (∀ (α : List (Fin 4)) (b : ℕ → RationalSpaceTime) (y : SpaceTime),
        IsFastName b y → ∀ (ε : ℚ) (hε : 0 < ε),
          ‖mixedDerivative f α y -
            rationalVector (evaluateCompiledExpandingForce C I hI a α b ε hε)‖ ≤ (ε : ℝ)) ∧
      (∀ (α : List (Fin 4)) (R : ℚ) (y : SpaceTime),
        (∀ j, |timeSpaceCoord j y| ≤ |(R : ℝ)|) →
        ‖mixedDerivative f α y‖ ≤ (compiledExpandingForceBound C I hI a α R : ℝ)) ∧
      WholePlaneDetection ν f I := by
  exact whole_plane_velocity_detection hE cylinder_local_energy_identity

end ForcedComputation.ExpandingDetector

end

end OAI
