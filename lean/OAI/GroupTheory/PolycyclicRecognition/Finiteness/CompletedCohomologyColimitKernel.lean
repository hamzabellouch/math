import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SequentialCohomologyKernel
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedSyzygyColimit
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedCohomology

namespace OAI

/-! # Detecting zero complete classes in a coefficient colimit

Under FP-infinity, a complete class whose image in the coefficient colimit is
zero already dies at a finite coefficient stage.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem normalizedCohomologyForward_comp (A : Rep.{0} ℤ G) (i j k : ℕ)
    (hij : i ≤ j) (hjk : j ≤ k) (x : normalizedCohomologyStage A i) :
    normalizedCohomologyForward A j k hjk (normalizedCohomologyForward A i j hij x) =
      normalizedCohomologyForward A i k (hij.trans hjk) x :=
  Module.DirectedSystem.map_map (f := normalizedCohomologyForward A) hij hjk x

theorem TypeFPInfinity.completedCohomology_colimit_kernel
    (hG : TypeFPInfinity G) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A) (i : ℕ)
    (x : CompletedCohomology (D.obj i)) (hx : completedCohomologyMap (c.ι i) x = 0) :
    ∃ (j : ℕ) (hij : i ≤ j), completedCohomologyMap (D.map i j hij) x = 0 := by
  obtain ⟨n, y, rfl⟩ := Module.DirectLimit.exists_of x
  rw [completedCohomologyMap_of] at hx
  obtain ⟨m, hnm, hm⟩ := Module.DirectLimit.of.zero_exact hx
  let z := normalizedCohomologyForward (D.obj i) n (m + 1) (hnm.trans (Nat.le_succ m)) y
  have hz : normalizedCohomologyStageMap (c.ι i) (m + 1) z = 0 := by
    rw [normalizedCohomologyForward_natural]
    rw [← normalizedCohomologyForward_comp A n m (m + 1) hnm (Nat.le_succ m), hm, map_zero]
  let E := D.mapFunctor (iteratedNormalizedSyzygy (m + 1))
  let ec := c.iteratedNormalizedSyzygy (m + 1)
  have hz' : groupCohomology.map (MonoidHom.id G) (ec.ι i) (m + 1) z = 0 := by
    rw [SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy_ι]
    exact hz
  obtain ⟨j, hij, hj⟩ := hG.cohomology_colimit_kernel E
    ((iteratedNormalizedSyzygy (m + 1)).obj A) ec m i z hz'
  refine ⟨j, hij, ?_⟩
  have hrepr := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := normalizedCohomologyStage (D.obj i)) (f := normalizedCohomologyForward (D.obj i))
    (hij := hnm.trans (Nat.le_succ m)) (x := y)
  change Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward (D.obj i)) (m + 1) z = _ at hrepr
  rw [← hrepr, completedCohomologyMap_of]
  have hj' : normalizedCohomologyStageMap (D.map i j hij) (m + 1) z = 0 := hj
  rw [hj', map_zero]

end PolycyclicRecognition

end

end OAI
