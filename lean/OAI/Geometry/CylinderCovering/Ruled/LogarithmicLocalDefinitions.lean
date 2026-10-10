import OAI.Geometry.CylinderCovering.Ruled.LocalDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.ProductLocal
open MeasureTheory RuledApproximation

def LogarithmicLocalStatement : Prop :=
  ∀ (D : Set Plane) (v : Plane → Plane) (h M : ℝ),
    IsCompact D → D.Nonempty → 0 < h → 0 < M → SmoothNear 1 D v →
    (∀ p ∈ D, HyperbolicAt M v p) →
    ∀ (eta m gamma : ℝ), 0 < eta → 1 < m → 0 < gamma →
      (1+gamma)*(1/m^2) < 1 → ProductCells.areaRatio (1/m^2) gamma ≤ 1+eta →
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ p ∈ D,
      ∀ (lam : ℝ) (L : (ℝ × ℝ) ≃L[ℝ] Plane),
      IsUnitEigenframe (fderiv ℝ v p) lam L → 0 < M*lam → M*lam < 1 →
      ∀ t : ℝ, 0 < t → t < t0 →
      affineCell p t L (ProductCells.logarithmicCell m) ⊆ D →
      ∃ C : Cylinder,
        C.axis = ‖vec3 1 (v p 0) (h*v p 1)‖⁻¹ • vec3 1 (v p 0) (h*v p 1) ∧
        C.carrier = firstPhysicalMap h '' auxiliaryCylinder
          (affineCell p t L (ProductCells.logarithmicIntercept m gamma)) (v p) ∧
        C.openBounded ∧
        physicalRuled h (affineCell p t L (ProductCells.logarithmicCell m)) v M ⊆ C.carrier ∧
        C.area ≤ h*(1+eta)^2 *
          (∫ q in affineCell p t L (ProductCells.logarithmicCell m), physicalWeight h (v q))

def SourceLogarithmicLocalStatement : Prop :=
  ∀ (X k : ℝ) (D : Set Plane) (v : Plane → Plane),
    0 < X → 0 < k → IsCompact D → D.Nonempty → OpenRectangleC2 D v →
    (∀ p ∈ D, LinearMap.trace ℝ Plane (fderiv ℝ v p).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ v p).toLinearMap < 0 ∧
      k*X*Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) < 1) →
    ∀ eta : ℝ, 0 < eta →
    ∃ m : ℝ, 1 < m ∧ ∃ gamma : ℝ, 0 < gamma ∧
      (1+gamma)*(1/m^2) < 1 ∧ ProductCells.areaRatio (1/m^2) gamma < 1+eta ∧
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ p ∈ D,
      ∀ (lam : ℝ) (L : (ℝ × ℝ) ≃L[ℝ] Plane),
      0 < lam → IsUnitEigenframe (fderiv ℝ v p) lam L →
      ∀ t : ℝ, 0 < t → t < t0 →
      affineCell p t L (ProductCells.logarithmicCell m) ⊆ D →
      ∃ C : Cylinder,
        C.axis = ‖vec3 1 (k*v p 0) (k*v p 1)‖⁻¹ • vec3 1 (k*v p 0) (k*v p 1) ∧
        C.carrier = firstPhysicalMap 1 '' auxiliaryCylinder
          (affineCell p t L (ProductCells.logarithmicIntercept m gamma)) (k • v p) ∧
        C.openBounded ∧
        physicalRuled 1 (affineCell p t L (ProductCells.logarithmicCell m))
          (fun q => k • v q) X ⊆ C.carrier ∧
        C.area ≤ (1+eta)^2 *
          (∫ q in affineCell p t L (ProductCells.logarithmicCell m),
            1 / Real.sqrt (1+k^2*‖v q‖^2))

def LogarithmicRemainderStatement : Prop :=
  ∀ (X k : ℝ) (D : Set Plane) (v : Plane → Plane),
    0 < X → 0 < k → IsCompact D → OpenRectangleC2 D v →
    (∀ p ∈ D, LinearMap.trace ℝ Plane (fderiv ℝ v p).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ v p).toLinearMap < 0) →
    ∀ m : ℝ, 1 < m → ∃ t0 B : ℝ, 0 < t0 ∧ 0 < B ∧
    ∀ p ∈ D, ∀ (lam : ℝ) (L : (ℝ × ℝ) ≃L[ℝ] Plane),
      0 < lam → IsUnitEigenframe (fderiv ℝ v p) lam L →
    ∀ t : ℝ, 0 < t → t < t0 →
    ∀ s ∈ ProductCells.logarithmicCell m, ∀ x : ℝ, |x| ≤ X →
      ∃ E : ℝ × ℝ,
        (let q := p + t • L s
         q + (x*k) • (v q-v p) =
           p + t • L (((1+x*k*lam)*s.1+E.1,(1-x*k*lam)*s.2+E.2))) ∧
        ‖vec2 E.1 E.2‖ ≤ B*t

def CompleteLocalStatement : Prop :=
  ProductCells.GeometryStatement ∧ LocalStatement ∧
    LogarithmicLocalStatement ∧ SourceLogarithmicLocalStatement ∧ LogarithmicRemainderStatement

end CylinderCovering.ProductLocal

end

end OAI
