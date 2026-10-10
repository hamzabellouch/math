import OAI.Geometry.CylinderCovering.Nilpotent.ApexNetDefinitions
import OAI.Geometry.RuledCovering.Model

namespace OAI

open Set MeasureTheory RuledApproximation

noncomputable section
namespace CylinderCovering.NilpotentApexNet

def planeTile (k ρ : ℝ) : Set Plane :=
  (fun q : ℝ × ℝ => vec2 q.1 q.2) '' tile k ρ

def planeVelocity (k σ p : ℝ) : Plane :=
  vec2 (velocity k σ p).1 (velocity k σ p).2

def physicalApexSweep (h k ρ σ : ℝ) : Set Space :=
  {z | ∃ s p t : ℝ, |s| ≤ 1 ∧ |p| ≤ 1 ∧ 0 ≤ t ∧ t ≤ ρ ∧
    z = vec3 s (p * t + s * (velocity k σ p).1)
      (h * (t + s * (velocity k σ p).2))}

def PhysicalApexNetStatement : Prop :=
  ∀ (h k ρ σ : ℝ), 0 < h → 0 ≤ k → 0 < ρ → ρ ≤ 1 → |σ| ≤ 1 →
    ∀ F : Space ≃ᵢ Space, ∃ C : Fin (meshCount ρ + 1) → Cylinder,
      (∀ j, (C j).parallelogram ∧ IsCompact (C j).base ∧
        Convex ℝ (C j).base ∧ MeasurableSet (C j).base ∧ volume (C j).base < ⊤ ∧
        (C j).carrier = F '' (firstPhysicalMap h '' auxiliaryCylinder (planeTile k ρ)
          (planeVelocity k σ (node ρ j))) ∧
        (C j).axis = F.toRealLinearIsometryEquiv
          (‖vec3 1 (planeVelocity k σ (node ρ j) 0) (h * planeVelocity k σ (node ρ j) 1)‖⁻¹ •
            vec3 1 (planeVelocity k σ (node ρ j) 0) (h * planeVelocity k σ (node ρ j) 1)) ∧
        (C j).area = h * weightedArea h k ρ σ j) ∧
      F '' physicalApexSweep h k ρ σ ⊆ familySet C ∧
      familyArea C ≤ h * (16 * (1 + k / 2) ^ 2 * ρ)

def FullApexNetStatement : Prop :=
  AuxiliaryApexNetStatement ∧ PhysicalApexNetStatement

end CylinderCovering.NilpotentApexNet

end

end OAI
