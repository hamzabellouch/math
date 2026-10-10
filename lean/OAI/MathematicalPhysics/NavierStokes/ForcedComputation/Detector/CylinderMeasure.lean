import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! The product of planar volume and one unit of vertical period. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set

def verticalPeriodMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure verticalPeriodMeasure := by
  constructor
  simp [verticalPeriodMeasure, Real.volume_Icc]

def cylinderMeasure : Measure (Plane × ℝ) :=
  (volume : Measure Plane).prod verticalPeriodMeasure

abbrev CylinderL2 := Lp ℝ 2 cylinderMeasure

def CylinderContinuousL2 (F : ℝ → Plane × ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ U : ℝ → CylinderL2, ContinuousOn U S ∧
    ∀ t ∈ S, (fun x => U t x) =ᵐ[cylinderMeasure] F t

def CylinderC1L2 (F G : ℝ → Plane × ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ U V : ℝ → CylinderL2, ContinuousOn U S ∧ ContinuousOn V S ∧
    ∀ t ∈ S, ((fun x => U t x) =ᵐ[cylinderMeasure] F t) ∧
      ((fun x => V t x) =ᵐ[cylinderMeasure] G t) ∧ HasDerivWithinAt U (V t) S t

end ForcedComputation.VelocityDetector

end

end OAI
