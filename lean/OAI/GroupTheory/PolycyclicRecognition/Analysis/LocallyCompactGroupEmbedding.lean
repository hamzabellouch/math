import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.UniformSpace.CompleteSeparated

namespace OAI

/-! # A locally compact embedded subgroup is closed -/

noncomputable section
namespace PolycyclicRecognition
open Filter Topology

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem closedEmbedding_of_locallyCompact_group [LocallyCompactSpace G] [T0Space H]
    (f : G →* H) (hf : Topology.IsEmbedding f) : Topology.IsClosedEmbedding f := by
  let uG : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  let uH : UniformSpace H := IsTopologicalGroup.rightUniformSpace H
  let rG : IsRightUniformGroup G := { uniformity_eq := rfl }
  let complete : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace G
  have hu : IsUniformEmbedding f := by
    refine ⟨⟨?_⟩, hf.injective⟩
    simp only [IsRightUniformGroup.uniformity_eq, show uniformity H =
      comap (fun p : H × H => p.2 * p.1⁻¹) (𝓝 (1 : H)) from rfl,
      comap_comap, Function.comp_def]
    rw [show (fun p : G × G => f p.2 * (f p.1)⁻¹) =
      f ∘ (fun p : G × G => p.2 * p.1⁻¹) by
        funext p; simp only [Function.comp_apply, map_mul, map_inv]]
    rw [← comap_comap]
    rw [← f.map_one, ← hf.isInducing.nhds_eq_comap]
  exact hu.isClosedEmbedding

end PolycyclicRecognition

end

end OAI
