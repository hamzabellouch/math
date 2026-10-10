import OAI.Geometry.CylinderCovering.Beams.sDefinitions
import OAI.Geometry.CylinderCovering.Beams.CostDefinitions
import OAI.Geometry.CylinderCovering.Radial.RiemannDefinitions
import OAI.Geometry.TriangularCovering.Basic

namespace OAI

open Filter
open scoped Topology
noncomputable section
namespace ShortenedBeam

def CoverageStatement : Prop :=
  ∀ a : ℝ, 0 < a → a < 1/2 →
    IsCompact (beamMinus a) ∧ IsCompact (beamPlus a) ∧
    tetrahedron ⊆ beamMinus a ∪ beamPlus a ∪ strip a

def FiniteBeamsStatement : Prop :=
  ∀ a : ℝ, 0 < a → a < 1/2 →
  ∀ tag : (N : ℕ) → Fin N → ℝ,
    (∀ N, CylinderCovering.RadialRiemann.IsTagged 0 1 N (tag N)) →
    ∃ Cminus Cplus : (N : ℕ) → Fin N → TriangularCovering.TriCylinder,
      (∀ N, 0 < N →
        (∀ i, (Cminus N i).axis = axisMinus a (tag N i) ∧
          (Cplus N i).axis = axisPlus a (tag N i)) ∧
        (∀ z ∈ beamMinus a, ∃ i : Fin N, z ∈ (Cminus N i).carrier) ∧
        (∀ z ∈ beamPlus a, ∃ i : Fin N, z ∈ (Cplus N i).carrier)) ∧
      Tendsto (fun N => TriangularCovering.totalArea (Cminus N) +
        TriangularCovering.totalArea (Cplus N)) atTop
        (𝓝 ((Real.sqrt 2/4)*CylinderCovering.BeamCost.beamCost a))

end ShortenedBeam

end

end OAI
