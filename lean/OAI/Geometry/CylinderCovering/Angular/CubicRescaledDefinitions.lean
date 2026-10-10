import OAI.Geometry.CylinderCovering.Cubic.RescalingDefinitions
import OAI.Geometry.CylinderCovering.Angular.ConstructionDefinitions

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace CylinderCovering.Cubic
open TriangularCovering

def FullCubicRescaledStatement : Prop :=
  contraction '' K4 = K ∧
  (∀ a b : ℝ, a ≤ b →
    IsGreatest (TriangularCovering.d '' Icc a b)
      (max (TriangularCovering.d a) (TriangularCovering.d b))) ∧
  (∀ τ a b : ℝ, cap (τ / 2) a b / 2 =
    1 / 2 + τ ^ 2 *
      (max (TriangularCovering.d a) (TriangularCovering.d b) + 25 / 4 * τ)) ∧
  Tendsto (fun τ : ℝ => 25 / 4 * τ) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
  RescaledFiniteCoverStatement ∧
  (∀ τ : ℝ, 0 < τ → τ ≤ 1 →
    |cubicCost (τ / 2) / (4 * H) - (1 / 2 - τ ^ 2 / 240)| ≤
      (401 / 4 : ℝ) * τ ^ 3) ∧
  ((fun τ : ℝ => cubicCost (τ / 2) / (4 * H) - (1 / 2 - τ ^ 2 / 240))
    =O[𝓝[>] (0 : ℝ)] (fun τ => τ ^ 3)) ∧
  ∃ delta : ℝ, 0 < delta ∧
    ∀ τ : ℝ, 0 < τ → τ < delta →
      ∃ C : Fin (2 * n (τ / 2)) → TriCylinder,
        Covers C ∧ ContractedFamily (τ / 2) C ∧
        totalArea C = cubicCost (τ / 2) / 4 ∧ totalArea C < A_min / 2

end CylinderCovering.Cubic

end

end OAI
