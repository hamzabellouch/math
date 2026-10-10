import OAI.Geometry.CylinderCovering.Angular.CubicCoverDefinitions

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace CylinderCovering.Cubic
open TriangularCovering

def minimumShadow4 : ℝ :=
  sInf {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = area (projection u '' K4)}

def FullCubicStatement : Prop :=
  minimumShadow4 = 4 * H ∧
  FiniteCoverStatement ∧
  (∀ eps : ℝ, 0 < eps → eps ≤ 1 / 2 →
    |cubicCost eps / H - (2 - eps ^ 2 / 15)| ≤ 3208 * eps ^ 3) ∧
  ((fun eps : ℝ => cubicCost eps - (2 * H - H / 15 * eps ^ 2))
    =O[𝓝[>] (0 : ℝ)] (fun eps => eps ^ 3)) ∧
  ∃ delta : ℝ, 0 < delta ∧
    ∀ eps : ℝ, 0 < eps → eps < delta →
      ∃ C : Fin (2 * n eps) → TriCylinder,
        CoversK4 C ∧ PrescribedFamily eps C ∧
        totalArea C = cubicCost eps ∧ totalArea C < minimumShadow4 / 2

end CylinderCovering.Cubic

end

end OAI
