import OAI.Geometry.CylinderCovering.Footprints.CertificatesDefinitions
import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
namespace CylinderCovering.Footprints

def physicalChart (p : ℝ × ℝ) : RuledApproximation.Plane :=
  RuledApproximation.vec2 p.2 (1-p.1)

def physicalLabelSet (F : Set (ℝ × ℝ)) : Set RuledApproximation.Plane :=
  physicalChart '' F

def quadraticVelocity (ε c : ℝ) : RuledApproximation.Plane :=
  RuledApproximation.vec2 (-ε*((1+c^2)/2)) (ε*c)

def quadraticSweepPoint (h ε x q ρ : ℝ) : RuledApproximation.Space :=
  RuledApproximation.vec3 x (ρ*q-ε*x*((1+q^2)/2)) (h*(1-ρ+ε*x*q))

def quadraticDirection (h ε c : ℝ) : RuledApproximation.Space :=
  RuledApproximation.vec3 1 (-ε*((1+c^2)/2)) (h*(ε*c))

def physicalFootprintProjection (h ε c : ℝ) (p : ℝ × ℝ) : RuledApproximation.Space :=
  let z := RuledApproximation.vec3 0 p.2 (h*(1-p.1))
  let v := quadraticDirection h ε c
  z - (inner ℝ v z / ‖v‖^2) • v

def PhysicalFootprintRealization : Prop :=
  ∀ (h ε c : ℝ) (F : Set (ℝ × ℝ)), 0 < h →
    ∃ C : RuledApproximation.Cylinder,
      C.axis = ‖quadraticDirection h ε c‖⁻¹ • quadraticDirection h ε c ∧
      Subtype.val '' C.base = physicalFootprintProjection h ε c '' F ∧
      C.area = h * MeasureTheory.volume.real F /
        Real.sqrt (1+ε^2*(((1+c^2)/2)^2+h^2*c^2)) ∧
      (IsCompact F → IsCompact C.base) ∧
      (Convex ℝ C.base ↔ Convex ℝ F) ∧
      (∀ x q ρ : ℝ, quadraticIntercept ε x q c ρ ∈ F →
        quadraticSweepPoint h ε x q ρ ∈ C.carrier) ∧
      (∃ f : (ℝ × ℝ) →ᵃ[ℝ]
          ((Submodule.span ℝ ({C.axis} : Set RuledApproximation.Space))ᗮ),
        Function.Injective f ∧ C.base = f '' F ∧
          ∀ p, (f p : RuledApproximation.Space) = physicalFootprintProjection h ε c p)

structure PhysicalFootprintCertificates : Prop where
  local_certificates : LocalFootprintCertificates
  physical_realization : PhysicalFootprintRealization

end CylinderCovering.Footprints

end

end OAI
