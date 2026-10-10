import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RuledApproximation

def PhysicalProjectionStatement : Prop :=
  ∀ (h : ℝ) (T : Set Plane) (g : Plane),
    0 < h → Bornology.IsBounded T → MeasurableSet T →
    ∀ F : Space ≃ᵢ Space, ∃ C : Cylinder,
      C.carrier = F '' (firstPhysicalMap h '' auxiliaryCylinder T g) ∧
      C.axis = F.toRealLinearIsometryEquiv
        (‖vec3 1 (g 0) (h * g 1)‖⁻¹ • vec3 1 (g 0) (h * g 1)) ∧
      C.area = h * volume.real T * physicalWeight h g ∧
      MeasurableSet C.base ∧ Bornology.IsBounded C.base ∧ volume C.base < ⊤ ∧
      (IsOpen T → IsOpen C.base) ∧
      (IsCompact T → IsCompact C.base) ∧
      (IsParallelogram T → C.parallelogram)

end RuledApproximation

end

end OAI
