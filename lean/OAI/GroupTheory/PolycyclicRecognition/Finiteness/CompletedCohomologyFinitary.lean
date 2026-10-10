import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedCohomology

namespace OAI

/-! # Sequential zero-finitarity of degree-zero complete cohomology

Every element has a representative in one ordinary cohomology degree. The
normalized syzygy functors preserve vanishing coefficient systems, and FP in
that degree kills the representative at a later coefficient stage.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem TypeFPInfinity.completedCohomology_eventually_zero
    (hG : TypeFPInfinity G) (D : SequentialRepresentationDiagram G) (hD : D.Vanishes)
    (i : ℕ) (x : CompletedCohomology (D.obj i)) :
    ∃ (j : ℕ) (hij : i ≤ j), completedCohomologyMap (D.map i j hij) x = 0 := by
  obtain ⟨n, y, rfl⟩ := Module.DirectLimit.exists_of x
  let E := D.mapFunctor (iteratedNormalizedSyzygy n)
  have hE : E.Vanishes := D.vanishes_iteratedNormalizedSyzygy hD n
  let : Subsingleton E.ModuleLimit := E.vanishes_iff_limit_subsingleton.mp hE
  obtain ⟨j, hij, hj⟩ := TypeFP.cohomology_eventually_zero E.obj E.map n (hG n) i y
  refine ⟨j, hij, ?_⟩
  rw [completedCohomologyMap_of]
  have hj' : normalizedCohomologyStageMap (D.map i j hij) n y = 0 := hj
  exact (congrArg (Module.DirectLimit.of ℤ ℕ _
    (normalizedCohomologyForward (D.obj j)) n) hj').trans (map_zero _)

end PolycyclicRecognition

end

end OAI
