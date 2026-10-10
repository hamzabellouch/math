import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SequentialCohomologySurjectivity
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedCohomologyColimitKernel

namespace OAI

/-! # Every complete class lifts from a finite coefficient stage under FP-infinity -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem TypeFPInfinity.completedCohomology_colimit_surj
    (hG : TypeFPInfinity G) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A) (x : CompletedCohomology A) :
    ∃ (i : ℕ) (y : CompletedCohomology (D.obj i)), completedCohomologyMap (c.ι i) y = x := by
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  let E := D.mapFunctor (iteratedNormalizedSyzygy n)
  let ec := c.iteratedNormalizedSyzygy n
  obtain ⟨i, y, hy⟩ := hG.cohomology_colimit_surj E
    ((iteratedNormalizedSyzygy n).obj A) ec n z
  change normalizedCohomologyStage (D.obj i) n at y
  refine ⟨i, Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward (D.obj i)) n y, ?_⟩
  rw [completedCohomologyMap_of]
  have hy' : normalizedCohomologyStageMap (c.ι i) n y = z := by
    rw [SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy_ι] at hy
    exact hy
  rw [hy']

theorem TypeFPInfinity.completedCohomology_colimit_subsingleton
    (hG : TypeFPInfinity G) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A)
    (hz : ∀ i, Subsingleton (CompletedCohomology (D.obj i))) :
    Subsingleton (CompletedCohomology A) := by
  apply subsingleton_of_forall_eq (0 : CompletedCohomology A)
  intro x
  obtain ⟨i, y, rfl⟩ := hG.completedCohomology_colimit_surj D A c x
  rw [(hz i).elim y 0, map_zero]

end PolycyclicRecognition

end

end OAI
