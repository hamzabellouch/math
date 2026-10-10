import OAI.Geometry.CylinderCovering.Barycentric.FiniteDefinitions

namespace OAI

noncomputable section
namespace RadialCoordinates

def canonicalToBary (z : Space) : BarycentricSpace :=
  barycentricPoint ((z 2 / Real.sqrt 2 + 1) / 2) (z 0 / 2) (z 1 / 2)

def canonicalEmbedding : Space →ₗ[ℝ] BarycentricSpace where
  toFun z := !₂[z 0 / Real.sqrt 2 + z 2 / 2,
    -z 0 / Real.sqrt 2 + z 2 / 2,
    z 1 / Real.sqrt 2 - z 2 / 2,
    -z 1 / Real.sqrt 2 - z 2 / 2]
  map_add' z w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r z := by
    ext i
    fin_cases i <;> simp <;> ring

def canonicalCenter : BarycentricSpace := !₂[1/4,1/4,1/4,1/4]

def canonicalScale : ℝ := 1 / (2 * Real.sqrt 2)

def canonicalCap (k q : ℝ) : ℝ := 2 * cap k ((q+1)/2)

end RadialCoordinates

end

end OAI
