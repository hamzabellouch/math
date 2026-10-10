import OAI.Geometry.CylinderCovering.Singular.EdgeOneGeometryDefinitions

namespace OAI

noncomputable section
namespace SingularEdgeOne
open RuledApproximation

def labelLinear : Plane ≃ₗ[ℝ] Plane where
  toFun := labelMap
  invFun z := vec2 (2 * z 0) (z 1)
  left_inv := by
    intro z
    ext i
    fin_cases i <;> simp [labelMap, vec2]
    ring
  right_inv := by
    intro z
    ext i
    fin_cases i <;> simp [labelMap, vec2]
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp [labelMap, vec2]
    ring
  map_smul' := by
    intro c z
    ext i
    fin_cases i <;> simp [labelMap, vec2]
    ring

def labelContinuous : Plane ≃L[ℝ] Plane := labelLinear.toContinuousLinearEquiv

def edgeHamiltonian (p w l : ℝ) : ℝ :=
  (2 : ℝ) ^ (p - 3) * (w ^ 2 * l ^ (p - 2) - l ^ p / 4)

end SingularEdgeOne

end

end OAI
