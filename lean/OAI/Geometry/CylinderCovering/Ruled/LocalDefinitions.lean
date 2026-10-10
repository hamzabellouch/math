import OAI.Geometry.CylinderCovering.Ruled.CellsDefinitions
import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
namespace CylinderCovering.ProductLocal
open MeasureTheory RuledApproximation

def affineCell (p : Plane) (rho : ℝ) (L : (ℝ × ℝ) ≃L[ℝ] Plane)
    (S : Set (ℝ × ℝ)) : Set Plane := (fun s => p + rho • L s) '' S

def IsUnitEigenframe (A : Plane →L[ℝ] Plane) (lam : ℝ)
    (L : (ℝ × ℝ) ≃L[ℝ] Plane) : Prop :=
  ‖L (1,0)‖ = 1 ∧ ‖L (0,1)‖ = 1 ∧
  A (L (1,0)) = lam • L (1,0) ∧
  A (L (0,1)) = (-lam) • L (0,1)

def LocalStatement : Prop :=
  ∀ (D : Set Plane) (v : Plane → Plane) (h M : ℝ),
    IsCompact D → D.Nonempty → 0 < h → 0 < M → SmoothNear 1 D v →
    (∀ p ∈ D, HyperbolicAt M v p) →
    ∀ (eta tau gamma : ℝ), 0 < eta → 0 < tau → tau < 1 → 0 < gamma →
      (1+gamma)*tau < 1 → ProductCells.areaRatio tau gamma ≤ 1+eta →
    ∃ rho0 : ℝ, 0 < rho0 ∧ ∀ p ∈ D,
      ∀ (lam : ℝ) (L : (ℝ × ℝ) ≃L[ℝ] Plane),
      IsUnitEigenframe (fderiv ℝ v p) lam L → 0 < M*lam → M*lam < 1 →
      ∀ rho : ℝ, 0 < rho → rho < rho0 →
      affineCell p rho L (ProductCells.parameterCell tau) ⊆ D →
      ∃ C : Cylinder,
        C.axis = ‖vec3 1 (v p 0) (h*v p 1)‖⁻¹ • vec3 1 (v p 0) (h*v p 1) ∧
        C.carrier = firstPhysicalMap h '' auxiliaryCylinder
          (affineCell p rho L (ProductCells.interceptCell tau gamma)) (v p) ∧
        C.openBounded ∧
        physicalRuled h (affineCell p rho L (ProductCells.parameterCell tau)) v M ⊆ C.carrier ∧
        C.area ≤ h*(1+eta)^2 *
          (∫ q in affineCell p rho L (ProductCells.parameterCell tau), physicalWeight h (v q))

end CylinderCovering.ProductLocal

end

end OAI
