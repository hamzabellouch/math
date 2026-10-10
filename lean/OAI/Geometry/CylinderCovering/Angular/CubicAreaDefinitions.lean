import OAI.Geometry.CylinderCovering.Angular.MarginsDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.Cubic

def speedSq (l r : ℝ) : ℝ := alpha l r ^ 2 + 2 * beta l r ^ 2

def areaTerm (eps l r : ℝ) : ℝ :=
  (r - l) * cap eps l r ^ 2 / Real.sqrt (1 + eps ^ 2 * speedSq l r)

def areaDensity (q : ℝ) : ℝ := -(1 / 8 : ℝ) - q ^ 2 / 4 + 7 * q ^ 4 / 8

def areaSum (eps : ℝ) (N : ℕ) : ℝ :=
  ∑ j : Fin N, areaTerm eps (node N j) (node N (j + 1))

end CylinderCovering.Cubic

end

end OAI
