import OAI.Geometry.CylinderCovering.Angular.CubicCoverDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.Cubic
open TriangularCovering

def contraction (p : Space) : Space := point 0 0 (1 / 2) + (1 / 2 : ℝ) • p

def contractedBaseMap (u p : Space) : Space :=
  projection u (point 0 0 (1 / 2)) + (1 / 2 : ℝ) • p

def ContractedFamily (ε : ℝ) (c : Fin (2 * n ε) → TriCylinder) : Prop :=
  ∃ original : Fin (2 * n ε) → TriCylinder, PrescribedFamily ε original ∧
    ∀ i, (c i).axis = (original i).axis ∧
      (c i).base = contractedBaseMap (original i).axis '' (original i).base

def RescaledFiniteCoverStatement : Prop :=
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
    n (τ / 2) = ⌈8 / τ ^ 2⌉₊ ∧
    ∃ c : Fin (2 * n (τ / 2)) → TriCylinder,
      Covers c ∧ totalArea c = cubicCost (τ / 2) / 4 ∧ ContractedFamily (τ / 2) c

end CylinderCovering.Cubic

end

end OAI
